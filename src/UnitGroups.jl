################################################################################
#
#  Unit group of quotients
#
################################################################################

mutable struct UnitGroupPresentation{S}
  Q
  abelian_groups
  to_abelian_groups
  to_quotient
  P
  to_P
  from_P
  ugens
  ugensinv
  phi
  S

  function UnitGroupPresentation{S}(Q, abelian_groups, to_abelian_groups, to_quotient, P, to_P, from_P) where {S}
    return new{S}(Q, abelian_groups, to_abelian_groups, to_quotient, P, to_P, from_P)
  end
end

function Oscar.image(U::UnitGroupPresentation, y)
  @assert parent(y) === codomain(U)
  return U(y)
end

function Oscar.preimage(U::UnitGroupPresentation, x)
  z = U.to_abelian_groups(one(U.Q))
  auts = U.from_P(x)
  U.to_quotient([image(hom(auts[i]), z[i]) for i in 1:length(auts)])
end

mutable struct UnitGrpMap{S, T}
  Q::S
  G::T
  U
  image_fun
  preimage_fun
end

Oscar.image(f::UnitGrpMap, x) = f.image_fun(x)

Oscar.preimage(f::UnitGrpMap, x) = f.preimage_fun(x)

function embed_quotient_into_product_of_abelian_groups(S, Q; split = true)
  O = Q.base_ring
  F = Q.ideal
  moduli = _compute_a_complete_coprime_splitting(O, F; split = split)
  abelian_groups = abelian_group_type(S)[]
  for m in moduli
    filter(!isone, elementary_divisors(quo(O, m * O)[1].basis_matrix))
    bmat = Hecke.basis_matrix_wrt(m, O)
    @assert isone(denominator(bmat))
    A = abelian_group(S, numerator(bmat))
    push!(abelian_groups, A)
  end

  k = length(moduli)

  to_abelian_groups = function(x)
    @assert parent(x) === Q
    c = coordinates(x.elem)
    return [A(c) for A in abelian_groups]
  end

  to_quotient = function(y)
    @assert all(parent(y[i]) == abelian_groups[i] for i in 1:k)
    els = elem_type(O)[]
    for i in 1:k
      yic = y[i].coeff
      push!(els, O([yic[1, l] for l in 1:ncols(yic)]))
    end
    return Q(crt(els, moduli))
  end

  abelian_groups, to_abelian_groups, to_quotient
end

function get_endomorphism_from_right_multiplication(a, abelian_groups, to_abelian_groups, to_quotient)
  homs = []
  x = [id(A) for A in abelian_groups]
  nab = length(abelian_groups)
  for i in 1:nab
    A = abelian_groups[i]
    k = ngens(A)
    imgs = elem_type(A)[]
    for j in 1:k
      x[i] = gen(A, j)
      y = to_abelian_groups(to_quotient(x) * a)
      @assert all(is_zero(y[l]) for l in 1:nab if l != i)
      push!(imgs, y[i])
    end
    push!(homs, hom(A, A, imgs))
    x[i] = id(A)
  end
  homs = identity.(homs)
  return homs
end

function get_automorphism_from_right_multiplication(a, abelian_groups, to_abelian_groups, to_quotient)
  m = get_endomorphism_from_right_multiplication(a, abelian_groups, to_abelian_groups, to_quotient)
  @assert all(is_bijective, m)
  return m
end

function product_of_auts_to_permutation_group(abgrps::Vector)
  isos = []
  @vprintln :SFC "Computing permutation representations of Aut(R^+)"
  for A in abgrps
    @vprint :SFC "R^+ = $(elementary_divisors(A)) ..."
    iso = isomorphism(PermGroup, automorphism_group(A))
    @vprintln :SFC " permutation degree $(degree(codomain(iso)))"
    push!(isos, iso)
  end
  isos = identity.(isos)
  @vprintln :SFC "Computing inner product of permutation groups"
  P, injs, projs = inner_direct_product([codomain(iso) for iso in isos], morphisms = true)
  n = length(abgrps)
  forward = function(a::Vector)
    elts = [image(injs[i], image(isos[i], domain(isos[i])(a[i]))) for i in 1:n]
    el = one(P)
    for e in elts
      el = el * e
    end
    return el
  end
  backward = function(x)
    @assert parent(x) === P
    elts = [preimage(isos[i], image(projs[i], x)) for i in 1:n] # elements from the automorphim groups
  end
  return P, forward, backward
end

function UnitGroupPresentation(Q; split = true)
  return UnitGroupPresentation(OscarGroup, Q; split = split)
end

function UnitGroupPresentation(::Type{S}, Q; split = true) where {S}
  abelian_groups, to_abelian_groups, to_quotient = embed_quotient_into_product_of_abelian_groups(S, Q, split = split)
  P, to_P, from_P = product_of_auts_to_permutation_group(abelian_groups)
  return UnitGroupPresentation{S}(Q, abelian_groups, to_abelian_groups, to_quotient, P, to_P, from_P)
end

function (U::UnitGroupPresentation)(a)
  @assert parent(a) === U.Q
  m = get_automorphism_from_right_multiplication(a, U.abelian_groups, U.to_abelian_groups, U.to_quotient)
  return U.to_P(m)
end

function Oscar.codomain(U::UnitGroupPresentation)
  return U.P
end

global UNIT_GROUP_CACHE = IdDict()

function unit_group_quotient_raw(Q, gens = nothing; split = true, maximal_order = nothing)
  return unit_group_quotient_raw(OscarGroup, Q, gens; split = split, maximal_order = maximal_order)
end

function unit_group_quotient_raw(::Type{T}, Q, gens = nothing; split = true, maximal_order = nothing) where {T}
  if haskey(UNIT_GROUP_CACHE, (T, Q))
    return UNIT_GROUP_CACHE[(T, Q)]
  end

  O = Q.base_ring
  F = Q.ideal

  if gens !== nothing
    ugens = gens::Vector{elem_type(Q)}
    #ugens = Q.(Hecke.K1_order_mod_conductor(O, M, F, do_units = true))
  else
    ugens = unit_group_generators(Q)
    #ugens = Q.(Hecke.K1_order_mod_conductor(O, maximal_order, F, do_units = true))
  end

  @vprintln :SFC "Computing embedding of Aut(R^+)"
  @v_do :SFC pushindent()
  U = UnitGroupPresentation(T, Q, split = split)
  @v_do :SFC popindent()
  @vprint :SFC "Computing generators of R^* and the image ..."
  ugroupgens = [U(u) for u in ugens]
  U.ugens = ugens
  U.ugensinv = inv.(ugens)
  G = codomain(U)
  S, mS = sub(U.P, ugroupgens)
  @vprintln :SFC "done"
  #phi = GAP.Globals.EpimorphismFromFreeGroup(S.X)
  #U.phi = phi
  #U.S = S

  f = function(x)
    if !is_unit(x)
      error("Element not a unit")
    end
    return preimage(mS, U(x))
  end

  g = function(s)
    return preimage(U, image(mS, s))
  end

  mU = UnitGrpMap(Q, S, U, f, g)

  UNIT_GROUP_CACHE[(T, Q)] = (S, mU)
  
  return S, mU
end

function unit_group_quotient_matrices(::Type{T}, Q, gens = nothing) where {T}
  if haskey(UNIT_GROUP_CACHE, (T, Q, :matrix))
    return UNIT_GROUP_CACHE[(T, Q, :matrix)]
  end

  O = Q.base_ring
  F = Q.ideal
  if gens !== nothing
    ugens = gens::Vector{elem_type(Q)}
    #ugens = Q.(Hecke.K1_order_mod_conductor(O, M, F, do_units = true))
  else
    ugens = unit_group_generators(Q)
    #ugens = Q.(Hecke.K1_order_mod_conductor(O, maximal_order, F, do_units = true))
  end
  B = Q.basis_matrix
  @assert B == B[1, 1] * identity_matrix(ZZ, nrows(B))
  p = B[1, 1]
  @assert is_prime(p)
  BB = basis(O)
  F = GF(p, cached = false)
  mat = dense_matrix_type(F)[]
  for u in ugens
    M = change_base_ring(F, Hecke.representation_matrix_mod(u.elem, p))
    push!(mat, M)
  end
  #G = GL(nrows(B), F)
  #S, = sub(G, G.(mat))
  #S, mS, magmaF = magma_matrix_group(mat)
  @vprintln :SFC 1 "Construction matrix group"
  S = matrix_group(T, mat)
  @vprintln :SFC 1 "Setting up maps ..."
  #phi = GAP.Globals.EpimorphismFromFreeGroup(S.X)
  ugensinv = inv.(ugens)
  basis_as_matrices = dense_matrix_type(F)[]
  for b in BB
    push!(basis_as_matrices, change_base_ring(F, Hecke.representation_matrix_mod(b, p)))
  end

  big_matrix = matrix([Hecke._eltseq(m) for m in basis_as_matrices])

  f = function(y)
    @assert parent(y) === Q
    @assert is_unit(y)
    mm = change_base_ring(F, Hecke.representation_matrix_mod(y.elem, p))
    #mmm = oscar_matrix_to_magma_matrix(magmaF, mm)
    return S(mm)
    #return magma_matrix_to_matrix_group(S, mmm)
  end

  g = function(x)
    #o = element_to_element(x, phi, ugens, ugensinv, Q)
    # this is to slow to write something in the generators
    mm = matrix(F, 1, nrows(B)^2, Hecke._eltseq(x))
    fl, u = can_solve_with_solution(big_matrix, mm, side = :left)
    return Q(O(lift.(Ref(ZZ), Hecke._eltseq(u))))
  end

  mU = UnitGrpMap(Q, S, nothing, f, g)
  return S, mU
  #return big_matrix
end

function unit_group_quotient(Q, gens = nothing; split = true, maximal_order = nothing)
 return unit_group_quotient(OscarGroup, Q, gens; split = split, maximal_order = maximal_order)
end

function unit_group_quotient(::Type{T}, Q, gens = nothing; split = true, maximal_order = nothing) where {T}
  O = Q.base_ring
  F = Q.ideal
  if gens !== nothing
    ugens = gens::Vector{elem_type(Q)}
    #ugens = Q.(Hecke.K1_order_mod_conductor(O, M, F, do_units = true))
  else
    ugens = unit_group_generators(Q)
    #ugens = Q.(Hecke.K1_order_mod_conductor(O, maximal_order, F, do_units = true))
  end
  return unit_group_quotient_raw(T, Q, gens; split = split, maximal_order = maximal_order)
end

function unit_group_generators(Q)
  R = base_ring(Q)
  I = Q.ideal
  M = maximal_order(R)
  ugens = Q.(Hecke.K1_order_mod_conductor(R, M, I, do_units = true))
end

function _compute_a_complete_coprime_splitting(O, F; split = true)
  if !split
    return [F]
  end
  A = algebra(O)
  Z, ZtoA = center(A)
  OZ = maximal_order(Z)
  FinZ = Hecke._as_ideal_of_smaller_algebra(ZtoA, F)
  # this is g = F \cap Z = F \cap O_Z
  OinZ = Hecke._as_order_of_smaller_algebra(ZtoA, O, maximal_order(O))
  OinZ2 = order(Z, [has_preimage_with_preimage(ZtoA, b)[2] for b in basis(intersect(ZtoA(1 * OZ), O))])
  #@show OinZ == OinZ2

  facFinZ = factor(FinZ* OZ)
  
  primary_dec = primary_decomposition(FinZ, OinZ)

  primary_ideals = Vector{Tuple{Hecke.ideal_type(O), Hecke.ideal_type(O)}}()

  for (q, p) in primary_dec
    pO = Hecke._as_ideal_of_larger_algebra(ZtoA, p, O)
    qO = Hecke._as_ideal_of_larger_algebra(ZtoA, q, O)
    # The qO are primary ideals such that F = \prod (qO + F)
    push!(primary_ideals, (pO, qO))
  end

  moduli = Vector{Hecke.ideal_type(O)}()
  for i = 1:length(primary_ideals)
    push!(moduli, primary_ideals[i][2] + F)
  end

  if prod(moduli; init = 1 * O) != F
    error("Could not determine coprime splitting")
  end

  return moduli
end

# Assume I \subseteq J
# (R/I)^* -> (R/J)^* is surjective
# The kernel is ((1 + J) \cap (R/I))/(1 + I)
# We enumerate the kernel by enumerating J/I and checking which element is
# invertible in R/I
function kernel_of_unit_group_map(R, I, J)
  @assert is_one(denominator(basis_matrix(I) * inv(basis_matrix(J))))
  RmodQ, RtoRmodQ = quo(R, I)
  Quo, QuotoR = _quo_as_abelian_group(J, I)
  @info elementary_divisors(Quo)
  @info "Iterating over J/I: $(order(Quo))"
  cnt = 0
  gens = elem_type(R)[]
  for g in Quo
    cnt += 1
    if cnt % 10000 == 0
      @info "So far: $cnt"
    end
    el = R(1 + QuotoR(g))
    if is_unit(RtoRmodQ(el))
      push!(gens, el)
    end
  end
  @info "Found $(length(gens)) generators"
  return gens
end
