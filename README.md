# The stably free cancellation property of orders

This repository contains code accompanying the paper "Determination of the stably free cancellation property for orders" ([arXiv:2407.02294](https://arxiv.org/abs/2407.02294))
by W. Bley, T. Hofmann and H. Johnston.

## Installation

1. The software requires version >= 1.10 of julia (see [https://julialang.org/install/](https://julialang.org/install/)).
3. Start julia.
2. If Magma is not available, run
```julia-repl
julia> using Pkg; Pkg.add(url = "https://github.com/thofma/TestingSFC.jl", rev = "master")
```

If [Magma](http://magma.maths.usyd.edu.au/) is availabe and it should be used for some runtime critical subroutines, run

```julia-repl
julia> using Pkg; Pkg.add(url = "https://github.com/thofma/TestingSFC.jl", rev = "magma")
```

## Usage

The main functionality of the package is provided by the functions `has_SFC` and `has_SFC_naive`, which implement Algorithm 8.9 and Algorithm 10.3 (applied to the "Eichler splitting" of the algebra) respectively.

```julia
julia> using TestingSFC

julia> set_verbosity_level(:SFC, 1); # enables debug printing

julia> QG = group_algebra(QQ, dicyclic_group(16));

julia> ZG = integral_group_ring(QG);

julia> has_SFC(ZG)
```

## Examples from the manuscript

The following functions will run the algorithms for the examples from the paper. Note that the non-Magma version might take a very long time to finish for the groups of order >= 192.

```julia
# Theorem 9.4
check_not_sfc()

# Theorem 6.6
check_48_32()

# Theorem 13.1
check_288_409()  
check_480_266()
check_192_1022()
check_96_66()    #
check_240_94()
check_192_183()
check_384_580()
check_480_962()
```
