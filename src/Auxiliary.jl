################################################################################
#
#  Helpers
#
################################################################################

################################################################################
#
#  Locally radical ideals
#
################################################################################

# Test if f \cap O is locally radical and if not, make it locally radical
function is_locally_radical_with_adjustment(ML, f)
  A = algebra(f)
  Z, ZtoA = center(A)
  finZ = Hecke._as_ideal_of_smaller_algebra(ZtoA, f)
  OC = maximal_order(Z)
  finZ.order = OC
  n = norm(finZ)
  OC = maximal_order(Z)
  facfinZ = factor(finZ)
  newg = finZ
  for p in prime_divisors(ZZ(n))
    for P in prime_ideals_over(OC, p)
      if !haskey(facfinZ, P)
        newg = newg * P
      end
    end
  end
  if newg != finZ
    @vprintln :SFC "Conductor is not locally radical (Hyptohesis (F) not satisfied), adjusting ..."
    f = Hecke._as_ideal_of_larger_algebra(ZtoA, newg, ML)
    return false, f
  else
    @vprintln :SFC "Conductor is locally radical (Hyptohesis (F) satisfied)"
    return true, f
  end
end

################################################################################
#
#  Given O and two-sided ideal f, compute (O_C^+)^*/(v((O/f)^*))
#
################################################################################

function compute_ray_class_group(O, f; GRH::Bool = true)
  A = algebra(O)
  C, mC = center(A)
  g = Hecke._as_ideal_of_smaller_algebra(mC, f)
  ramified_places = Hecke.ramified_infinite_places_of_center(A)
  OC = maximal_order(C)
  #@assert g * OC == g
  R, OCtoR = ray_class_group(g*OC, ramified_places; GRH = GRH)
  #@assert O*f == f
  #Q, OtoQ = quo(O, f*O)
  f.order = O
  Q, OtoQ = quo(O, f)
  U = unit_group_generators(Q)
  ulifts = Vector{elem_type(A)}(undef, length(U))
  for i in 1:length(U)
    u = uu = elem_in_algebra(OtoQ\U[i])
    fl, = is_invertible(uu)
    j = 0
    while !fl
      u = uu + rand(f, 10)
      fl, = is_invertible(u)
      j += 1
      if j > 1000
        error("something wrong")
      end
    end
    ulifts[i] = u
  end

  img = [ OCtoR\(Hecke.normred_over_center(u, mC)*OC) for u in ulifts]
  Rquo, RtoRquo = quo(R, img)
  return OC, mC, OCtoR, RtoRquo
end

function _setup_maps_as_abelian_groups(f, R, S)
  rR = degree(R)
  rS = degree(S)
  A = algebra(R)
  RasAb = free_abelian_group(rR)
  SasAb = free_abelian_group(rS)
  h = hom(RasAb, SasAb, [SasAb(coordinates(S(f(elem_in_algebra(b))))) for b in basis(R)])
  return h
end

function basis_of_kernel(f, R, S)
  h = _setup_maps_as_abelian_groups(f, R, S)
  rR = degree(R)
  rS = degree(S)
  K, KtoRasAb = kernel(h)
  @assert isfree(K)
  BK = [elem_in_algebra(R([KtoRasAb(g).coeff[i] for i in 1:rR])) for g in gens(K) if !iszero(g)]
  @assert length(BK) == rR - rS
  return BK
end

function _unit_reps_combined(M, F; GRH::Bool = true)
  uus = Hecke._unit_reps(M, F; GRH = GRH)
  k = length(uus)
  res = elem_type(algebra(M))[]
  @vprintln :SFC 1 "Length of the individual T's: $(length.(uus)) (|T2| =  $(prod(length.(uus))))"
  if prod(length.(uus)) > 10^7
    error("Too many units in T2 ($(prod(length.(uus))))")
  end
  for u in Iterators.product(uus...)
    uu = sum((u[i]) for i in 1:k; init = zero(algebra(M)))
    push!(res, uu)
    #@assert abs(norm((uu))) == 1
  end
  return res
end

function _T2(F; GRH::Bool = true)
  if isdefined(F, :T2)
    return F.T2
  else
    F.T2 = _unit_reps_combined(F.M2, F.f2; GRH = GRH)
    return F.T2
  end
end

function quo_by_many_elements(G, elts)
  elts = deepcopy(elts)
  first_elts = eltype(elts)[]
  for i in 1:50
    if isempty(elts)
      break
    end
    push!(first_elts, popfirst!(elts))
  end
  Q, mQ = quo(G, first_elts)
  S, StoQ = snf(Q)
  mQ = mQ * inv(StoQ)
  Q = S
  while !isempty(elts)
    g = popfirst!(elts)
    if iszero(mQ(g))
      continue
    end
    Q, _mQ = quo(Q, [mQ(g)])
    mQ = mQ * _mQ
    S, StoQ = snf(Q)
    Q = S
    mQ = mQ * inv(StoQ)
  end
  return Q, mQ
end

function Oscar.isomorphism(::Type{FinGenAbGroup}, Q)
  O = Q.base_ring
  F = Q.ideal
  bmat = Hecke.basis_matrix_wrt(F, O)
  @assert isone(denominator(bmat))
  A = abelian_group(numerator(bmat))
  S, StoA = snf(A)
  AtoS = inv(StoA)

  to_abelian_group = function(x)
    @assert parent(x) === Q
    c = coordinates(x.elem)
    return AtoS(A(c))
  end

  to_Q = function(y)
    return Q(O([StoA(y).coeff[l] for l in 1:degree(O)]))
  end

  S, to_Q, to_abelian_group
end

function _quo_as_abelian_group(I, J)
  d = degree(order(I))
  F = free_abelian_group(d)
  M = QQMatrix(basis_mat_inv(I))
  subgens = elem_type(F)[]
  for b in basis(J)
    coef = ZZ.(Oscar.coefficients(b) * M)
    push!(subgens, F(coef))
  end
  Q, FtoQ = quo(F, subgens)
  B = basis(I)
  Q, c -> begin; cc = FtoQ\c; sum(cc.coeff[1, i] * B[i] for i in 1:d); end
end

function _is_purely_noneichler(R::Hecke.AlgAssAbsOrd)
  A = algebra(R)
  dec = first.(decompose(A))
  n = length(dec)
  deccentral = map(B -> Hecke._as_algebra_over_center(B)[1], dec)
  noneichler = findall(!is_eichler, deccentral)
  return length(noneichler) == n
end

function Oscar.Hecke.find_small_group(G::Oscar.GAPGroup)
  smallid = small_group_identification(G)
  Gco = collect(G)
  GG, GtoGG, GGtoG = generic_group(Gco, *)
  _id, GGgood, GGgoodtoGG = Hecke.find_small_group(GG)
  @assert _id == smallid
  h = x -> GGtoG[GGgoodtoGG(x)]
  g, k = GGgood[rand(1:_id[1])], GGgood[rand(1:_id[1])]
  @assert h(g * k) == h(g) * h(k)
  return _id, GGgood, h
end


################################################################################

function Hecke._is_principal(::Type{Hecke._PIPDefault}, I, O; side::Symbol = :right, local_freeness = false)
  @info "Using new principal ideal test"
  @assert Hecke._test_ideal_sidedness(I, O, :right)
  d = denominator(I, O)
  I = d * I
  @assert side == :right
  M = maximal_order(O)
  if !local_freeness
    for p in prime_divisors(index(O, M))
      if !islocally_free(O, I, p, side = :right)[1]
        @vprint :PIP "Not locally free at $p\n"
        return false
      end
    end
  end
  _fl, _alpha = Hecke._isprincipal_maximal(I * M, M, :right)
  if !_fl
    return false
  end
  # Now is the time to make it coprime to the conductor
  f = Hecke._get_a_twosided_conductor(O, M)
  if !isone(f + I)
    II, sca = Hecke._coprime_integral_ideal_class_deterministic(I, f)
    _alpha2 = M(sca * _alpha)
    @assert _alpha2 * M == II * M
  else
    _alpha2 = M(_alpha)
    II = I
  end

  return _s1_method(O, elem_in_algebra(_alpha2), fiber_product_from_eichler_splitting(O, M))
end
