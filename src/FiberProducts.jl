################################################################################
#
#  Fiber product of orders
#
################################################################################

@attributes mutable struct FiberProductOrder{S, T, U, V, W, X, Y, Z}
  R::S
  R1::T
  R2::T
  M::S
  M1::T
  M2::T
  p1::U
  p2::U
  f::V
  ftilde1::V
  ftilde2::V
  f1::W
  f2::W
  e1::X
  e2::X
  T2::Vector{Y}
  sigma1_gens::Vector{Z}
  sigma2_gens::Vector{Z}

  FiberProductOrder{S, T, U, V, W, X, Y, Z}() where {S, T, U, V, W, X, Y, Z} = new{S, T, U, V, W, X, Y, Z}()
end

function swap(F::FiberProductOrder)
  return fiber_product(F.R, F.p2, F.p1, F.M)
end

function fiber_product(R, p1, p2, _M = nothing, _f = nothing)
  A1 = codomain(p1)
  A2 = codomain(p2)
  @vprintln :SFC 2 "Projecting order under p1"
  R1 = p1(R)
  @vprintln :SFC 2 "Projecting order under p2"
  R2 = p2(R)
  @vprintln :SFC 2 "Computing maximal order"
  if _M === nothing
    M = maximal_order(R)
  else
    M = _M
  end
  @vprintln :SFC 2 "Computing two-sided conductor"
  if _f === nothing
    f = Hecke._get_a_twosided_conductor(R, M)
  else
    f = _f
  end
  f1 = p1(f)

  S = typeof(R)
  T = typeof(R1)
  U = typeof(p1)
  V = typeof(f)
  W = typeof(f1)
  X = elem_type(domain(p1))
  Y = elem_type(A2)
  Z = elem_type(R)

  z = FiberProductOrder{S, T, U, V, W, X, Y, Z}()
  z.R = R
  z.R1 = R1
  z.R2 = R2
  z.M = M
  @vprintln :SFC 2 "Projecting maximal order under p1"
  z.M1 = p1(M)
  @vprintln :SFC 2 "Projecting maximal order under p1"
  z.M2 = p2(M)
  z.p1 = p1
  z.p2 = p2
  f2 = p2(f)
  z.f = f
  z.f1 = f1
  z.f2 = f2
  @vprintln :SFC 2 "Computing center of algebra"
  C, CtoA = center(algebra(R))
  @vprintln :SFC 2 "Decomposing center of algebra"
  dec = decompose(C)
  idems = [CtoA(BtoC(one(B))) for (B, BtoC) in dec]
  e1 = sum(e for e in idems if !iszero(p1(e)); init = zero(one(algebra(R))))
  z.e1 = e1
  z.e2 = one(algebra(R)) - z.e1
  return z
end

function ftilde1(F::FiberProductOrder)
  if isdefined(F, :ftilde1)
    return F.ftilde1
  else
    F.ftilde1 = F.f + intersect(F.e1 * F.M, F.R)
    return F.ftilde1
  end
end

function ftilde2(F::FiberProductOrder)
  if isdefined(F, :ftilde2)
    return F.tilde2
  else
    F.ftilde2 = F.f + intersect(F.e2 * F.M, F.R)
    return F.ftilde2
  end
end

@attr W function h1(F::FiberProductOrder{S, T, U, V, W}) where {S, T, U, V, W}
  return F.p1(intersect(F.e1 * F.M, F.R)) * F.R1
end

@attr W function h2(F::FiberProductOrder{S, T, U, V, W}) where {S, T, U, V, W}
  return F.p2(intersect(F.e2 * F.M, F.R)) * F.R2
end

#@attr Any function h(F::FiberProductOrder)
#  return h1(F) + h2(F)
#end

################################################################################
#
#  Fibre product from maximal Eichler splitting
#
################################################################################

function maximal_eichler_quotient_with_projection(A::Hecke.AbstractAssociativeAlgebra)
  v = Int[]
  dec = decompose(A)
  for i in 1:length(dec)
    B, = Hecke._as_algebra_over_center(dec[i][1])
    if is_eichler(B)
      push!(v, i)
    end
  end
  return Hecke.product_of_components_with_projection(A, v)
end

function fiber_product_from_eichler_splitting(R)
  get_attribute!(R, :fiber_product_eichler) do
    A = algebra(R)
    # this is the non-Eichler component
    A2, p2 = Hecke.maximal_eichler_quotient_with_projection(A)
    # this is the Eichler component
    A1, p1 = maximal_eichler_quotient_with_projection(A)
    F = fiber_product(R, p1, p2)
    return F
  end
end

function fiber_product_from_eichler_splitting(R, M)
  A = algebra(R)
  # this is the non-Eichler component
  A2, p2 = Hecke.maximal_eichler_quotient_with_projection(A)
  # this is the Eichler component
  A1, p1 = maximal_eichler_quotient_with_projection(A)
  F = fiber_product(R, p1, p2, M)
  return F
end

################################################################################
#
#  Fiber product from normal subgroup
#
################################################################################

function fiber_product_from_subgroup(R, mH)
  v = Int[]
  w = Int[]
  H = domain(mH)
  A = algebra(R)
  G = group(A)
  eH = QQ(1//order(H)) * sum(A(mH(h)) for h in H; init = zero(A))
  Q, GtoQ = quo(G, [mH(g) for g in gens(H)])
  dec = decompose(A)
  for i in 1:length(dec)
    B, BtoA = dec[i]
    if BtoA(one(B)) * eH != 0
      push!(v, i)
    else
      push!(w, i)
    end
  end
  A1, p1 =  Hecke.product_of_components_with_projection(A, v)
  A2, p2 = Hecke.product_of_components_with_projection(A, w)
  return fiber_product(R, p1, p2)
end

################################################################################
#
#  Check if some element has some preimage
#  Use for Algorithm 12.5 4(a)
#
################################################################################

# M = maximal order
# R = order
# f = two-sided ideal
# e1, e2 = central idempotents
# a2 element of M such that a2 in (e2M/e2f)^*
# p1 = A -> A1
# p2 = A -> A2
function _has_valid_first_component(F::FiberProductOrder, a2)
  @assert parent(a2) === algebra(F.R2)
  M2 = F.M2
  R = F.R
  f = F.f
  h, K, RtoQ = get_attribute!(F, :some_helpful_map) do
    h = _setup_maps_as_abelian_groups(F.p2, R, F.M2)
    K = basis_of_kernel(F.p2, R, F.M2)
    Q, RtoQ = quo(R, f)
    return h, K, RtoQ
  end
  # first find any preimag of a2 under R -> M2
  fl, c = has_preimage_with_preimage(h, codomain(h)(coordinates(F.M2(a2))))
  if !fl
    return false, zero(codomain(F.p1))
  end

  el = R([c.coeff[i] for i in 1:degree(R)])

  cnt = 0
  while !is_unit(RtoQ(el))
    el = el + R(dot(rand(-10:10, length(K)), K))
    cnt += 1
    if cnt >= 15000
      error("Asdsdds")
    end
  end

  b1 = F.p1(elem_in_algebra(el))
  #@assert b1 in F.M1
  F.f1.order = F.M1
  #Q2, M1toQ2 = quo(F.M1, F.f1)
  #@assert is_unit(M1toQ2(F.M1(b1)))
  return true, b1
end
