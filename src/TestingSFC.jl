module TestingSFC

using Reexport

@reexport using Oscar
@reexport using Hecke

function __init__()
  Hecke.add_verbosity_scope(:SFC)
end

export Oscar

abstract type OscarGroup end

abstract type MagmaGroup end

has_magma(x) = false

Oscar.abelian_group(::Type{OscarGroup}, x...; kw...) = Oscar.abelian_group(x...; kw...)

Oscar.matrix_group(::Type{OscarGroup}, x...; kw...) = Oscar.matrix_group(x...; kw...)

Oscar.maximal_abelian_quotient(::Type{OscarGroup}, x...; kw...) = Oscar.maximal_abelian_quotient(FinGenAbGroup, x...; kw...)

Oscar.Hecke._eltseq(x::MatrixGroupElem) = Oscar.Hecke._eltseq(matrix(x))

abelian_group_type(::Type{OscarGroup}) = FinGenAbGroup

double_coset_representatives(G::Oscar.GAPGroup, H::Oscar.GAPGroup, K::Oscar.GAPGroup) = elem_type(G)[representative(x) for x in double_cosets(G, H, K; check = false)]

abelian_group_aut_type(::Type{OscarGroup}) = AutomorphismGroup{FinGenAbGroup}

perm_group_type(::Type{OscarGroup}) = PermGroup

group_map_type(::Type{OscarGroup}, ::Type{A}, ::Type{B}) where {A, B} = GAPGroupHomomorphism{A, B}

function magma_setup
end

function unit_group_presentation
end

function mcall
end

function magma_matrix_group
end

function magma_matrix_to_oscar_matrix
end

function oscar_matrix_to_magma_matrix
end

function oscar_gf_to_magma_gf
end

function magma_matrix_to_matrix_group
end

function magma_abelian_group
end

function magma_hom
end

function magma_kernel
end

function magma_sub
end

function magma_derived_subgroup
end

function magma_abelian_quotient
end

function magma_abelian_quotient_slow
end

function magma_abelian_quotient_slow_of_matrix_group
end

function magma_quotient
end

import Hecke: pushindent, popindent

include("FiberProducts.jl")
include("Test.jl")
include("UnitGroups.jl")
include("UnitGroupAbelianization.jl")
include("Eichler.jl")
include("Reduction.jl")
include("Idempotents.jl")
include("Auxiliary.jl")
include("NotSFC.jl")
include("Naive.jl")
include("TestLattices.jl")
include("PIP.jl")
include("Paper.jl")
include("find_interesting_SFC_groups_order_512.jl")
include("find_interesting_SFC_groups.jl")

export has_SFC
export has_SFC_naive
export fiber_product_from_subgroup
export reduction

export MagmaGroup
export OscarGroup
# UnitGroupViaFiniteRings

default_group_type() = _default_group_type(true)

_default_group_type(::Any) = OscarGroup

function has_SFC(O::Hecke.AlgAssAbsOrd; GRH = false)
  return has_SFC(default_group_type(), O; GRH = GRH)
end

function has_SFC(::Type{T}, O::Hecke.AlgAssAbsOrd; GRH = false) where {T}
  return proof_via_standard_eichler_splitting(T, O; GRH = GRH)
end

function has_SFC_naive(O::Hecke.AlgAssAbsOrd; GRH = false)
  return has_SFC_naive(default_group_type(), O; GRH = GRH)
end

function has_SFC_naive(::Type{T}, O::Hecke.AlgAssAbsOrd; GRH = false) where {T}
  return has_stably_free_cancellation_naive(T, O; GRH = GRH)
end

#function has_SFC_via_fibre_product(F::FiberProductOrder, O::AlgAssAbsOrd;
#  check_corners = :both)
#end
#
#function has_not_SFC_heuristic(O::AlgAssAbsOrd; freeness_test = :rigorous) # or heuristic
#  @warn "The result is not rigorous, but only a heuristic"
#end

end # module TestingSFC
