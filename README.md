This repository contains the implementation of the algorithms presented in the master's thesis
"Computing Ham-Sandwich Cuts for Polytopes".

Brief Description of the Files:
The implementation is written in Julia. We use Oscar.jl for computations
in algebraic geometry, and HomotopyContinuation.jl for solving the polynomial
systems arising from the algorithm.

The repository is organised into three folders:

    Halving_Hyperplanes_dim2/: Implementation and examples in dimension 2.
                               Contains a Jupyter notebook illustrating the
                               computation of halving hyperplanes.

    Halving_Hyperplanes_dim3/: Implementation and examples in dimension 3.
                               Contains a Jupyter notebook illustrating the
                               computation of halving hyperplanes.

    Halving_Hyperplanes_d/:    General implementation for arbitrary fixed dimension. 
                               Also includes an implementation for arbitrary α-proportions.
