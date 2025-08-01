export check_not_sfc
export check_48_32
export check_288_409
export check_480_266
export check_192_1022
export check_96_66
export check_240_94
export check_192_183
export check_384_580
export check_480_962

# Helper

# Functions to compute units

function _cyclic_units(ZG)
  QG = algebra(ZG)
  G = group(QG)
  orders = [order(g) for g in G]
  G = [ZG(QG(g)) for g in G]
  units = copy(G)
  for i in 1:length(G)
    d = orders[i]
    g = G[i]
    @assert is_one(g^d)
    for h in G
      u = 1 + (g - 1) * h * sum([g^i for i in 0:d-1])
      @assert is_one(abs(norm(elem_in_algebra(u))))
      push!(units, u)
      u = 1 + sum([g^i for i in 0:d-1]) * h * (g - 1)
      @assert is_one(abs(norm(elem_in_algebra(u))))
      push!(units, u)
    end
  end
  return unique!(units)
end

# Functions to find fiber products
function has_good_quotient(G)
  Ns = normal_subgroups(G)
  cur_min = order(G)
  local Nbest
  for N in Ns
    if order(N) == order(G)
      continue
    end
    Q, = quo(G, N)
    if has_obviously_sfc(Q)
      if order(N) < cur_min
        Nbest = N
        cur_min = order(N)
        continue
      end
    end
  end
  if cur_min == order(G)
    return false, (G, nothing)
  else
    return true, (Nbest, hom(Nbest, G, gens(Nbest)))
  end
end

function has_obviously_sfc(G)
  X = character_table(G)
  quat = 0
  for x in X
    if degree(x) == 2 && indicator(x) == -1
      quat += 1
    end
  end
  return quat <= 1
end

function has_good_fiber_product(ZG)
  @vprintln :SFC 1 "Trying to find useful fiber product"
  fl, (S, StoG) = has_good_quotient(group(algebra(ZG)))
  if fl
    @vprintln :SFC 1 "Yes, with index $(order(S))"
    return true, TestingSFC.fiber_product_from_subgroup(ZG, StoG)
  else
    return false, nothing
  end
end

# Functions to compute ZG, ZH, ZC2xH and Gamma for a given normal subgroup.

# Compute Gamma given G and G/N = H
function compute_relevant_orders(grpid, quotid)
  G = small_group(grpid...)
  local S, StoG
  local H
  for g in G
    if order(g) != divexact(grpid[1], quotid[1])
      continue
    end
    S, StoG = sub(G, [g])
    if !is_normalized_by(S, G)
      continue
    end
    H = quo(G, S)
    if small_group_identification(H[1]) == quotid
      break
    end
  end
  QG = QQ[G]
  ZG = Order(QG, basis(QG), isbasis = true)
  @assert Oscar.small_group_identification(quo(G, S)[1]) == quotid
  trN = sum(QG(StoG(s)) for s in S)
  Gamma, =  Hecke.quotient_order(ZG, trN * ZG)
  QH = QQ[H[1]]
  ZH = Order(QH, basis(QH), isbasis = true)
  HC2 = direct_product(H[1], small_group(2, 1))
  QHC2 = QQ[HC2]
  ZHC2 = Order(QHC2, basis(QHC2), isbasis = true)
  return ZG, ZH, Gamma, ZHC2
end

function find_group_and_subgroup(grpid, quotid)
  G = small_group(grpid...)
  local S, StoG
  local H
  for g in G
    if order(g) != divexact(grpid[1], quotid[1])
      continue
    end
    S, StoG = sub(G, [g])
    if !is_normalized_by(S, G)
      continue
    end
    H = quo(G, S)
    if small_group_identification(H[1]) == quotid
      break
    end
  end
  @assert Oscar.small_group_identification(quo(G, S)[1]) == quotid
  return G, StoG
end

#GRH = false

function check_48_32(; GRH = false)
  G = small_group(24, 3) # \tilde{T}
  Tt = G
  QG = QQ[G]
  ZG = integral_group_ring(QG)
  ZTt = ZG
  C = locally_free_class_group(ZG; GRH = GRH)
  @vprintln :SFC 1 "Locally free class group of tildeT: $(elementary_divisors(C))"
  @assert order(C) == 2
  G = small_group(48, 32)
  QG = QQ[G]
  ZG = integral_group_ring(QG)
  C = locally_free_class_group(ZG; GRH = GRH)
  @vprintln :SFC 1 "Locally free class group of tildeT x C2: $(elementary_divisors(C))"
  @assert order(C) == 2^6
  @vprintln :SFC 1 "Checking size of V"
  u = _cyclic_units(ZTt)
  Q, ZTttoQ = quo(ZTt, 2*ZTt)
  _, mU = unit_group_quotient_matrices(default_group_type(), Q)
  Ugens = [image(mU, ZTttoQ(u)) for u in u]
  U, = sub(parent(Ugens[1]), Ugens) 
  @assert order(U) == 3*2^17
  @vprintln :SFC 1 "Found U <= V with |U| = 3*2^17"
end

# Theorem 9.4

function check_not_sfc(; GRH = false)
  ids = [(16, 12),
         (32, 41),
         (40, 7),
         (96, 198),
         #(96, 188),
         #(240, 94),
         (32, 14),
         (36, 7),
         (64, 14),
        ]
  for id in ids
    @vprintln :SFC 1 "Checking not SFC of canonical quotient for $id (GRH = $GRH)"
    @v_do :SFC 1 Hecke.pushindent()
    G = small_group(id...)
    QG = QQ[G]
    ZG = integral_group_ring(QG)
    @vtime :SFC fl = !TestingSFC.sfc_of_canonical_quotient(ZG; GRH = GRH)
    @assert fl
    @v_do :SFC 1 Hecke.popindent()
  end

  @vprintln :SFC 1 "Checking not SFC for (100, 7) (GRH = $GRH)"
  @v_do :SFC 1 Hecke.pushindent()
  # for 100, 7 we have to do something different
  G = small_group(100, 7)
  QG = QQ[G]
  ZG = integral_group_ring(QG)
  dec = decompose(QG)
  ind = findall(!iseichler, first.(dec))
  found = false
  @vtime :SFC for v in subsets(ind, 3)
    _, p = Hecke.product_of_components_with_projection(QG, v)
    Gamma = p(ZG)
    fl = TestingSFC.has_not_stably_free_cancellation_probably(Gamma; repetitions = 100, GRH = GRH)
    if fl
      found = true
      break
    end
  end
  @v_do :SFC 1 Hecke.popindent()
  @assert found
end

function compute_class_group_orders(grpid, quotid; GRH)
  @vprintln :SFC 1 "Computing the orders"
  ZG, ZH, Gamma, ZHC2 = compute_relevant_orders(grpid, quotid)
  tZG = @elapsed CZG = locally_free_class_group(ZG; GRH = GRH)
  hZG = order(CZG)
  tZH = @elapsed CZH = locally_free_class_group(ZH; GRH = GRH)
  hZH = order(CZH)
  tZHC2 = @elapsed CZHC2 = locally_free_class_group(ZHC2; GRH = GRH)
  hZHC2 = order(CZHC2)
  tGamma = @elapsed CGamma = locally_free_class_group(Gamma; GRH = GRH)
  hGamma = order(CGamma)
  @vprintln :SFC 1 "Locally free class group of Z[G]: $(elementary_divisors(CZG)) $(factor(hZG)) $(round(Int, tZG))s"
  @vprintln :SFC 1 "Locally free class group of Z[H]: $(elementary_divisors(CZH)) $(factor(hZH)) $(round(Int, tZH))s"
  @vprintln :SFC 1 "Locally free class group of Z[HxC2]: $(elementary_divisors(CZHC2)) $(factor(hZHC2)) $(round(Int, tZHC2))s"
  @vprintln :SFC 1 "Locally free class group of Gamma: $(elementary_divisors(CGamma)) $(factor(hGamma)) $(round(Int, tGamma))s"
  return CZG, CZH, CZHC2, CGamma, ZG, ZH, ZHC2, Gamma
end

check_96_66(;GRH = false, skip_class_groups = false) = check_96_66(TestingSFC.default_group_type(); GRH = GRH, skip_class_groups)

function check_96_66(::Type{T}; GRH = false, skip_class_groups = false) where {T}
  @vprintln :SFC 1 "96, 66"
  # 96, 66
  # Q_8 sd Q_12
  if !skip_class_groups
    CZG, CZH, CZHC2, CGamma, _, _, _, Gamma = compute_class_group_orders((96, 66), (48, 29); GRH)
    @assert order(CZG) == 512
    @assert order(CZH) == 2
    @assert order(CZHC2) == 128
    @assert order(CGamma) == 8
    @assert order(CZG) * order(CZH) == order(CZHC2) * order(CGamma)
    @assert TestingSFC.has_SFC(T, Gamma, GRH = GRH)
    return true
  else
    _, _, Gamma, _ = compute_relevant_orders((96, 66), (48, 29))
    @vtime :SFC fl = TestingSFC.has_SFC(T, Gamma; GRH = GRH)
    @assert fl
    return true
  end
end

check_288_409(;GRH = false, skip_class_groups = false) = check_288_409(TestingSFC.default_group_type(); GRH = GRH, skip_class_groups)

function check_288_409(::Type{T}; GRH = false, skip_class_groups = false) where {T}
  # needs Magma
  # 288, 409
  # \tilde{T} x Q_12
  @vprintln :SFC 1 "288, 409"
  if !(skip_class_groups)
    CZG, CZH, CZHC2, CGamma, _, _, _, Gamma = compute_class_group_orders((288, 409), (144, 127); GRH)
    @assert order(CZG) == ZZ(2)^28 * ZZ(3)^7
    @assert order(CZH) == ZZ(2)^5 * ZZ(3)^3
    @assert order(CZHC2) == ZZ(2)^23 * ZZ(3)^7
    @assert order(CGamma) == ZZ(2)^10 * ZZ(3)^3
    @assert order(CZG) * order(CZH) == order(CZHC2) * order(CGamma)
    @vtime :SFC fl = TestingSFC.has_SFC(T, Gamma, GRH = GRH)
    @assert fl
    return true
  else
    _, _, Gamma, _ = compute_relevant_orders((288, 409), (144, 127))
    @vtime :SFC fl = TestingSFC.has_SFC(T, Gamma, GRH = GRH)
    @assert fl
    return true
  end
end

check_480_266(;GRH = false, skip_class_groups = false) = check_480_266(TestingSFC.default_group_type(); GRH = GRH, skip_class_groups)

function check_480_266(::Type{T}; GRH = false, skip_class_groups) where {T}
  # 480, 266
  # \tilde{T} x Q_{20}
  @vprintln :SFC 1 "480, 266"

  if !(skip_class_groups)
    CZG, CZH, CZHC2, CGamma, _, _, _, Gamma = compute_class_group_orders((480, 266), (240, 108); GRH)
    @assert order(CZG) == ZZ(2)^41 * ZZ(3)^3
    @assert order(CZH) == ZZ(2)^9 * ZZ(3)^1
    @assert order(CZHC2) == ZZ(2)^34 * ZZ(3)^3
    @assert order(CGamma) == ZZ(2)^16 * ZZ(3)^1
    @vtime :SFC fl = TestingSFC.has_SFC(T, Gamma; GRH = GRH)
    @assert fl
    return true
  else
    _, _, Gamma, _ = compute_relevant_orders((480, 266), (240, 108))
    @vtime :SFC fl = TestingSFC.has_SFC(T, Gamma; GRH = GRH)
    @assert fl
    return true
  end
end

check_240_94(;GRH = false, skip_class_groups = false) = check_240_94(TestingSFC.default_group_type(); GRH = GRH, skip_class_groups)

function check_240_94(::Type{T};GRH = false, skip_class_groups = false) where {T}
  # 240, 94
  # C2 x \tilde{I}
  @vprintln :SFC 1 "240 94"

  if !(skip_class_groups)
    CZG, CZH, CZHC2, CGamma, _, _, _, Gamma = compute_class_group_orders((240, 94), (120, 35); GRH)
    @assert order(CZG) == ZZ(2)^10
    @assert order(CZH) == ZZ(2)
    @assert order(CZHC2) == ZZ(2)^6
    @assert order(CGamma) == ZZ(2)^5
    @vtime :SFC fl = TestingSFC.has_SFC(T, Gamma; GRH = GRH)
    @assert fl
    return true
  else
    @vtime :SFC fl = TestingSFC.has_SFC(T, Gamma; GRH = GRH)
    @assert fl
    return true
  end
end

#### Something else

check_192_1022(; GRH = false) = check_192_1022(TestingSFC.default_group_type(); GRH = GRH)

function check_192_1022(::Type{T}; GRH = false) where {T}
  G, HtoG = find_group_and_subgroup((192, 1022), (96, 204))
  QG = QQ[G]
  ZG = Hecke.integral_group_ring(QG)
  F = TestingSFC.fiber_product_from_subgroup(ZG, HtoG)
  @vtime :SFC fl = TestingSFC.reduction(T, F; use_matrices = true, GRH = GRH)
  @assert fl
  _, _, Gamma = compute_relevant_orders((192, 1022), (96, 204))
  @vprintln :SFC "Now prove SFC for Gamma"
  @vtime :SFC fl = TestingSFC.has_SFC(T, Gamma; GRH = GRH)
  @assert fl
  return true
end

check_192_183(; GRH = false) = check_192_183(TestingSFC.default_group_type(); GRH = GRH)

function check_192_183(::Type{T}; GRH = false) where {T}
  G, HtoG = find_group_and_subgroup((192, 183), (96, 66))
  QG = QQ[G]
  ZG = Hecke.integral_group_ring(QG)
  F = TestingSFC.fiber_product_from_subgroup(ZG, HtoG)
  @vtime :SFC fl = TestingSFC.reduction(T, F; use_matrices = true, GRH = GRH)
  @assert fl
  return true
end

check_384_580(; GRH = false) = check_384_580(TestingSFC.default_group_type(); GRH = GRH)

function check_384_580(::Type{T}; GRH = false) where {T}
  G, HtoG = find_group_and_subgroup((384, 580), (192, 183))
  QG = QQ[G]
  ZG = Hecke.integral_group_ring(QG)
  F = TestingSFC.fiber_product_from_subgroup(ZG, HtoG)
  @vtime :SFC fl = TestingSFC.reduction(T, F; use_matrices = true, GRH = GRH)
  @assert fl
  return true
end

check_480_962(; GRH = false) = check_480_962(TestingSFC.default_group_type(); GRH = GRH)

function check_480_962(::Type{T}; GRH = false) where {T}
  G, HtoG = find_group_and_subgroup((480, 962), (96, 66))
  QG = QQ[G]
  ZG = Hecke.integral_group_ring(QG)
  F = TestingSFC.fiber_product_from_subgroup(ZG, HtoG)
  @vtime :SFC fl = TestingSFC.reduction(T, F; use_matrices = true, GRH = GRH)
  @assert fl
  return true
end

################################################################################
#
#  Computing all centers
#
################################################################################

function _all_centers()
  res = [];
  #
  @vprintln :SFC 1 "24, 3"
  G = small_group(24, 3)
  QG = QQ[G]
  C, = center(QG)
  push!(res, ("24, 3", first.(Hecke._as_number_fields(C))))
  #
  @vprintln :SFC 1 "48, 32"
  G = small_group(48, 32)
  QG = QQ[G]
  C, = center(QG)
  push!(res, ("48, 32", first.(Hecke._as_number_fields(C))))
  #
  @vprintln :SFC 1 "100, 7"
  G = small_group(100, 7)
  QG = QQ[G]
  C, = center(QG)
  push!(res, ("100, 7", first.(Hecke._as_number_fields(C))))
  #
  @vprintln :SFC 1 "96 66"
  ZG, ZH, Gamma, ZHC2 = compute_relevant_orders((96, 66), (48, 29))
  QG = algebra(ZG)
  C, = center(QG)
  push!(res, ("96, 66", first.(Hecke._as_number_fields(C))))
  QHC2 = algebra(ZHC2)
  C, = center(QHC2)
  push!(res, ("48, 29 x C2", first.(Hecke._as_number_fields(C))))
  #
  @vprintln :SFC 1 "288 409"
  ZG, ZH, Gamma, ZHC2 = compute_relevant_orders((288, 409), (144, 127))
  QG = algebra(ZG)
  C, = center(QG)
  push!(res, ("288, 409", first.(Hecke._as_number_fields(C))))
  QHC2 = algebra(ZHC2)
  C, = center(QHC2)
  push!(res, ("144, 127 x C2", first.(Hecke._as_number_fields(C))))
  #
  @vprintln :SFC 1 "480, 266"
  ZG, ZH, Gamma, ZHC2 = compute_relevant_orders((480, 266), (240, 108))
  QG = algebra(ZG)
  C, = center(QG)
  push!(res, ("480, 266", first.(Hecke._as_number_fields(C))))
  QHC2 = algebra(ZHC2)
  C, = center(QHC2)
  push!(res, ("244, 108 x C2", first.(Hecke._as_number_fields(C))))
  #
  @vprintln :SFC 1 "192, 1022"
  G, HtoG = find_group_and_subgroup((192, 1022), (96, 204))
  QG = QQ[G]
  C, = center(QG)
  push!(res, ("192, 1022", first.(Hecke._as_number_fields(C))))
  #
  @vprintln :SFC 1  "192, 183"
  G, HtoG = find_group_and_subgroup((192, 183), (96, 66))
  QG = QQ[G]
  C, = center(QG)
  push!(res, ("192, 183", first.(Hecke._as_number_fields(C))))
  #
  @vprintln :SFC 1  "480 962"
  G, HtoG = find_group_and_subgroup((480, 962), (96, 66))
  QG = QQ[G]
  C, = center(QG)
  push!(res, ("480, 962", first.(Hecke._as_number_fields(C))))
  return res
end
