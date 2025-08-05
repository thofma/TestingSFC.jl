# The stably free cancellation property of orders

This repository contains code accompanying the paper "Determination of the stably free cancellation property for orders" ([arXiv:2407.02294](https://arxiv.org/abs/2407.02294))
by W. Bley, T. Hofmann and H. Johnston. The code works on linux and macOS systems.

## Installation

1. The software requires version >= 1.10 of julia (see [https://julialang.org/install/](https://julialang.org/install/)).
3. Start julia.
2. Run
```julia-repl
julia> using Pkg; pkg"up"; pkg"registry add https://github.com/thofma/Registry"; pkg"add TestingSFC, MagmaGroups";
```
Note that this will also install [Oscar](https://github.com/oscar-system/Oscar.jl/) (which might take a minute).

## Usage


> [!WARNING]  
> All positive results, where $\mathbf{Z}[G]$ is claimed to have stably free cancellation, are subject to the condition that some (and therefore every) maximal order containing $\mathbf{Z}[G]$ has stably free cancellation. This is not checked by the algorithm. For the examples in the README and the paper, this is guaranteed by theory.

The main functionality of the package is provided by the functions `has_SFC_naive` and `has_SFC`, which implement Algorithm 8.9 and Algorithm 10.3 (applied to the "Eichler splitting" of the algebra) respectively. Here is how one can use these functions to check that the integral group ring of the quaternion group of order $16$ has stably free cancellation. (In this case any maximal order has stably free cancellation by Corollary 4.6.)

```julia
julia> using TestingSFC # replace by `using TestingSFC, MagmaGroups` for faster version using magma subrountines

julia> set_verbosity_level(:SFC, 1); # enables debug printing

julia> QG = group_algebra(QQ, dicyclic_group(16));

julia> ZG = integral_group_ring(QG);

julia> has_SFC(ZG)
```
 
## Proofs for the paper

The following functions will run the algorithms which are part of the proofs from the paper. Note that the non-Magma version might take a very long time to finish for the groups of order >= 192.

```julia
# Theorem 6.6
check_48_32()

# Theorem 9.4
check_16_12()   # Q8 x C2
check_24_7()    # Q12 x C2
check_32_41()   # Q16 x C2
check_40_7(),   # Q20 x C2
check_96_198()  # Tt x C2^2
check_96_188()  # Ot x C2
check_480_960() # It x C2^2
check_32_14()
check_36_7()
check_64_14()
check_100_7()

# Theorem 13.1
check_288_409()  
check_480_266()
check_192_1022()
check_96_66()
check_240_94()
check_192_183()
check_384_580()
check_480_962()
```

## Using fiber products

A normal subgroup induces a fiber product for the integral group ring, see Section 6.1 of the paper. Assuming that one of the rings in the corner satisfies the Eichler condition, the stably free cancellation property can be reduced to the other corner using the function `reduction`:

```julia
julia> using TestingSFC # replace by `using TestingSFC, MagmaGroups` for faster version using magma subrountines

julia> set_verbosity_level(:SFC, 1); # enables debug printing

julia> G = small_group(48, 32);

julia> H = [ U for U in subgroups(G) if order(U) == 24][1];

julia> mH = hom(H, G, G.(gens(H))); # canonical map H -> G

julia> ZG = integral_group_ring(QQ[G]);

julia> F = fiber_product_from_subgroup(ZG, mH);

julia> reduction(F)
[...]
true
```
