################################################################################
#
#  Algorithms 12.5 and 12.12 (aka "S1-method")
#
################################################################################

# compute generators of S1 heuristically
function _s1_gens_heuristic(R, F = fiber_product_from_eichler_splitting(R); stabilize = 5)
  @vprintln :SFC 3 "Computing generators for S with the heuristic approach (stabilize = $stabilize)"
  @vprintln :SFC 3 "Computing the kernel of R/f -> R_2/f_2"
  h = _setup_maps_as_abelian_groups(F.p2, R, F.M2)
  K = basis_of_kernel(F.p2, R, F.M2)
  f = F.f
  Q, RtoQ = quo(R, f)
  @assert F.f2 * F.R2 == F.f2
  Q2, R2toQ2 = quo(F.R2, F.f2 * F.R2)
  # create Q -> Q2
  QA, QAtoQ, QtoQA = abelian_group(Q)
  Q2A, Q2AtoQ2, Q2toQ2A = abelian_group(Q2)
  ff = hom(QA, Q2A, [Q2toQ2A(R2toQ2(F.R2(F.p2(elem_in_algebra(preimage(RtoQ, QAtoQ(a))))))) for a in gens(QA)])
  KK, KKtoQA = kernel(ff)
  Kelements = preimage.(RtoQ, QAtoQ.(KKtoQA.(gens(KK))))

  cnt = 0

  @vprintln :SFC 3 "Computing unit group of quotient of O_C"

  A1 = algebra(F.M1)
  Z, ZtoA1 = center(A1)
  g1 = Hecke._as_ideal_of_smaller_algebra(ZtoA1, F.f1)
  OC = maximal_order(Z)
  Q, OCtoQ = quo(OC, g1)
  QU, QUtoQ = Hecke.unit_group(Q)
  final_quo, to_final_quo = quo(QU, [id(QU)])

  order_stable = 0
  cur_gens = elem_type(QU)[]
  non_unit = 0

  _Kelems, idems = _preimage_to_R2_helper(F)
  local_elts = Vector{elem_type(R)}(undef, length(idems))
  @vprintln :SFC 3 "Now computing random elements in the kernel"

  while true
    if cnt % 100 == 0
      @vprintln :SFC 3 "Current order of quotient: $(order(final_quo)); number of stabilizations: $(stabilize)"
    end

    if order_stable >= stabilize
      #@info "Order stable for $(stabilize) new elements"
      break
    end
    for i in 1:length(_Kelems)
      _cnt = 1
      while true
        if _cnt % 100 == 0
          @vprintln :SFC 3 "Hard to find proper unit at position $(i) ($(_cnt) tries)"
        end
        _cnt += 1
        _el = one(R) + mod(R(dot(rand(-1000:1000, length(_Kelems[i][1])), _Kelems[i][1])), _Kelems[i][3])
        if is_unit(_Kelems[i][2](_el))
          local_elts[i] = _el
          break
        end
      end
    end
    #el = crt(local_elts, splitf)
    el = sum(idems[i] * local_elts[i] for i in 1:length(idems))
    #@assert el - el2 in f
    #el = one(R) + R(dot(rand(-100:100, length(Kelements)), Kelements))
    cnt += 1
    #@info cnt, non_unit
    #if cnt % 100 == 0
    #  @info non_unit, cnt, order_stable
    #  #error("Asdsdds")
    #end
    #@assert is_unit(RtoQ(el))
    #if !is_unit(RtoQ(el))
    #  non_unit += 1
    #  continue
    #end
    @assert is_one(R2toQ2(F.R2(F.p2(elem_in_algebra(el)))))
    newelem = QUtoQ\(OCtoQ(OC(Hecke.normred_over_center(F.p1(elem_in_algebra(el)), ZtoA1))))
    push!(cur_gens, newelem)
    _final_quo, _to_final_quo = quo_by_many_elements(QU, cur_gens)
    if order(_final_quo) == order(final_quo)
      order_stable += 1
      pop!(cur_gens)
    else
      order_stable = 0
      final_quo, to_final_quo = _final_quo, _to_final_quo
    end

    if order_stable >= stabilize
      #@info "Order stable for $(stabilize) new elements"
      break
    end
  end

  #@info "Order of final quotient: $(order(final_quo)) (number of non-units: $(non_unit)/$(cnt))"

  return ZtoA1, QU, OC, OCtoQ, QUtoQ, final_quo, to_final_quo
end

# Rigorous computations of generators of S1
function _s1_gens_rigorous(R, F = fiber_product_from_eichler_splitting(R))
  A1 = algebra(F.M1)
  Z, ZtoA1 = center(A1)
  g1 = Hecke._as_ideal_of_smaller_algebra(ZtoA1, F.f1)
  OC = maximal_order(Z)
  Q, OCtoQ = quo(OC, g1)
  QU, QUtoQ = Hecke.unit_group(Q)
  sig_gen = _sigma_generators(F, 1)
  s1_gens = FinGenAbGroupElem[ QUtoQ\(OCtoQ(OC(Hecke.normred_over_center(F.p1(elem_in_algebra(b)), ZtoA1)))) for b in sig_gen]
  final_quo, to_final_quo = quo_by_many_elements(QU, s1_gens)
  #@info "Order of final quotient: $(order(final_quo))"
  return ZtoA1, QU, OC, OCtoQ, QUtoQ, final_quo, to_final_quo, s1_gens
end

function _s1_method(R, beta, F = fiber_product_from_eichler_splitting(R); s1_method = :rigorous, GRH::Bool = true)
  # maximal order of fiber product must be the parent of beta
  @assert beta in F.M
  @vprintln :SFC 2 "Calling improved PIP method with parameters ($(s1_method), GRH = $(GRH))"
  if s1_method == :rigorous
    T2, M2toQ, Q, ZtoA1, OC, OCtoQ, QUtoQ, to_final_quo, subtofinal_quo = get_attribute!(F, :s1_stuff_rigorous) do
      T2 = _T2(F; GRH = GRH)
      ZtoA1, QU, OC, OCtoQ, QUtoQ, final_quo, to_final_quo = _s1_gens_rigorous(R, F)
      OCu, OCumap = Hecke.unit_group(OC; GRH = GRH)
      subgrp_gens = [to_final_quo(QUtoQ\(OCtoQ(OCumap(u)))) for u in gens(OCu)]
      sub, subtofinal_quo = Hecke.sub(final_quo, subgrp_gens)
      F.f2.order = F.M2
      Q, M2toQ = quo(F.M2, F.f2)
      return T2, M2toQ, Q, ZtoA1, OC, OCtoQ, QUtoQ, to_final_quo, subtofinal_quo
    end
  elseif s1_method == :heuristic
    T2, M2toQ, Q, ZtoA1, OC, OCtoQ, QUtoQ, to_final_quo, subtofinal_quo = get_attribute!(F, :s1_stuff_heuristic) do
      T2 = _T2(F; GRH = GRH)
      ZtoA1, QU, OC, OCtoQ, QUtoQ, final_quo, to_final_quo = _s1_gens_heuristic(R, F)
      OCu, OCumap = Hecke.unit_group(OC; GRH = GRH)
      subgrp_gens = [to_final_quo(QUtoQ\(OCtoQ(OCumap(u)))) for u in gens(OCu)]
      sub, subtofinal_quo = Hecke.sub(final_quo, subgrp_gens)
      F.f2.order = F.M2
      Q, M2toQ = quo(F.M2, F.f2)
      return T2, M2toQ, Q, ZtoA1, OC, OCtoQ, QUtoQ, to_final_quo, subtofinal_quo
    end
  else
    error("Option s1_method = :$(s1_method) not valid in _s1_method")
  end
  @vprintln :SFC 2 "Need to iterator over #T2: $(length(T2))"

  beta2 = F.p2(beta)
  if det(Q.basis_matrix) == 1 # Q is the zero ring
    # We can't invert in the zero ring :(
    beta2inv = elem_in_algebra(M2toQ\(Q(F.M2(beta2))))
  else
    beta2inv = elem_in_algebra(M2toQ\(inv(Q(F.M2(beta2)))))
  end
  #@info "Multiplying with inv(beta2)"
  #T2beta2inv = [t * beta2inv for t in T2]
  beta1 = F.p1(beta)

  cnt = 0
  for t in T2
    a2 = t * beta2inv
    cnt += 1
    @vprintln :SFC 4 "cnt: $cnt/$(length(T2))"
    if cnt % 10^(min(4, clog(length(T2), 10) - 1)) == 0
      @v_do :SFC 2 pushindent()
      @vprintln :SFC 2 "cnt: $cnt (T2)"
      @v_do :SFC 2 popindent()
    end
    fl, b1 = _has_valid_first_component(F, a2)
    if fl
      el = to_final_quo(QUtoQ\(OCtoQ(OC(Hecke.normred_over_center(b1 * beta1, ZtoA1)))))
      fll, _ = has_preimage_with_preimage(subtofinal_quo, el)
      if fll
        return fll
      end
    end
  end
  return false
end

function _sigma_generators(F, i, do_maximal = false)
  ii = i
  @assert ii in [1, 2]
  if ii == 1 && isdefined(F, :sigma1_gens)
    @vprintln :SFC "Sigma generators cached"
    return F.sigma1_gens
  end
  if ii == 2 && isdefined(F, :sigma2_gens)
    @info "sigma2 generators cached"
    return F.sigma2_gens
  end

  f = F.f
  if ii == 1
    ftilde = ftilde1(F)
  else
    ftilde = ftilde2(F)
  end

  A = algebra(F.R)
  Z, ZtoA = center(A)
  if do_maximal
    R = F.M
  else
    R = F.R
  end

  @assert ftilde * R == ftilde

  OZ = maximal_order(Z)
  M = F.M
  LambdainZ = Hecke._as_order_of_smaller_algebra(ZtoA, R, M)
  finZ = Hecke._as_ideal_of_smaller_algebra(ZtoA, f)
  ftildeinZ = Hecke._as_ideal_of_smaller_algebra(ZtoA, ftilde)
  ftildeinZ = ftildeinZ * OZ
  @assert Hecke._test_ideal_sidedness(finZ, OZ, :left)
  @assert Hecke._test_ideal_sidedness(ftildeinZ, OZ, :left)

  facfinZ = Hecke.factor(finZ)
  prime_idealsf = Dict{Hecke.ideal_type(LambdainZ), Vector{Hecke.ideal_type(OZ)}}()
  for (p, e) in facfinZ
    q = contract(p, LambdainZ)
    if haskey(prime_idealsf, q)
      push!(prime_idealsf[q], p)
    else
      prime_idealsf[q] = [ p ]
    end
  end

  facftildeinZ = Hecke.factor(ftildeinZ)
  prime_idealsftilde = Dict{Hecke.ideal_type(LambdainZ), Vector{Hecke.ideal_type(OZ)}}()
  for (p, e) in facftildeinZ
    q = contract(p, LambdainZ)
    if haskey(prime_idealsftilde, q)
      push!(prime_idealsftilde[q], p)
    else
      prime_idealsftilde[q] = [ p ]
    end
  end

  primary_ideals_f = Vector{Tuple{Hecke.ideal_type(R), Hecke.ideal_type(R)}}()
  for p in keys(prime_idealsf)
    primes_above = prime_idealsf[p]
    q = primes_above[1]^facfinZ[primes_above[1]]
    for i = 2:length(primes_above)
      q = q*primes_above[i]^facfinZ[primes_above[i]]
    end
    pO = Hecke._as_ideal_of_larger_algebra(ZtoA, p, R)
    qO = Hecke._as_ideal_of_larger_algebra(ZtoA, contract(q, LambdainZ), R)
    # The qO are primary ideals such that F = \prod (qO + F)
    push!(primary_ideals_f, (pO, qO))
  end
  @assert f == prod(x[2] + f for x in primary_ideals_f)
  for (_,q1) in primary_ideals_f
    for (_,q2) in primary_ideals_f
      if q1 != q2
        @assert q1 + q2 + f == 1 * R
      end
    end
  end

  primary_ideals_ftilde = Vector{Tuple{Hecke.ideal_type(R), Hecke.ideal_type(R)}}()
  for p in keys(prime_idealsftilde)
    primes_above = prime_idealsftilde[p]
    q = primes_above[1]^facftildeinZ[primes_above[1]]
    for i = 2:length(primes_above)
      q = q*primes_above[i]^facftildeinZ[primes_above[i]]
    end
    pO = Hecke._as_ideal_of_larger_algebra(ZtoA, p, R)
    qO = Hecke._as_ideal_of_larger_algebra(ZtoA, contract(q, LambdainZ), R)
    # The qO are primary ideals such that F = \prod (qO + F)
    push!(primary_ideals_ftilde, (pO, qO))
  end
  @assert ftilde == prod(x[2] + ftilde for x in primary_ideals_ftilde; init = 1*order(ftilde))
  for (_,q1) in primary_ideals_ftilde
    for (_,q2) in primary_ideals_ftilde
      if q1 != q2
        @assert q1 + q2 + ftilde == 1 * R
      end
    end
  end

  # OK now comes the tricky part
  # The decomposition of f has potentially more prime ideals

  for (pO, qO) in primary_ideals_ftilde
    @assert any(x -> x[1] == pO, primary_ideals_f)
  end

  comps = Vector{elem_type(R)}[]

  moduli = Hecke.ideal_type(R)[]

  gensRmodf = Hecke.K1_order_mod_conductor(R, F.M, f, do_units = true)
  # The (R/f)^* computation wants a two-sided ideal contained in M
  # So we cannot call it for R/(qR + f), since qR + f is not an M-ideal.
  # But R/f -> R/(qR + f) is epimorphism of semilocal rings, hence induces
  # an epimorphism (R/f)^* -> R/(qR + f)^*

  for (pO, qO) in primary_ideals_f
    i = findfirst(x -> x[1] == pO, primary_ideals_ftilde)
    if i === nothing
      continue
    end
    qtildeO = primary_ideals_ftilde[i][2]
    Q = qO + f
    Q1 = qtildeO + f
    Qtilde = qtildeO + ftilde
  end

  for (pO, qO) in primary_ideals_f
    i = findfirst(x -> x[1] == pO, primary_ideals_ftilde)
    if i === nothing
      Q = qO + f
      for b in basis(R)
        for bb in basis(Q)
          @assert elem_in_algebra(b) * bb in Q
        end
      end
      RmodQ, RtoRmodQ = quo(R, Q)
      gens = [x for x in gensRmodf if !isone(RtoRmodQ(x))]
      #gens = Hecke.K1_order_mod_conductor(R, F.M, Q, do_units = true)
    else
      qtildeO = primary_ideals_ftilde[i][2]
      # We need to determine generators of the kernel of
      # R/qi + f -> R/qtildei + ftilde
      Q = qO + f
      Q1 = qtildeO + f
      Qtilde = qtildeO + ftilde
      if Q1 == Q
        gens = elem_type(R)[]
      else
        gens = Hecke._1_plus_p_mod_1_plus_q_generators(Q1, Q)
      end
      # Now we iterate of Qtilde/Q1 and check which
      if Qtilde != Q1
        RmodQ, RtoRmodQ = quo(R, Q)
        Quo, QuotoR = _quo_as_abelian_group(Qtilde, Q1)
        @vprintln :SFC 1 "Iterating over Qtilde/Q1; number of elements: $(order(Quo))"
        #@info "R mod Q $(elementary_divisors(quo(R, Q)[1].basis_matrix))"
        #@info "R mod Qtilde $(elementary_divisors(quo(R, Qtilde)[1].basis_matrix))"
        cnt = 0
        @v_do :SFC 1 pushindent()
        for g in Quo
          cnt += 1
          if cnt % 10000 == 0
            @vprintln :SFC 2 "So far: $cnt"
          end
          el = R(1 + QuotoR(g))
          if is_unit(RtoRmodQ(el))
            push!(gens, el)
          end
        end
        @v_do :SFC 1 popindent()
      end
    end
    push!(comps, gens)
    push!(moduli, Q)
  end

  final_gens = Hecke.make_coprime(comps, moduli)
  Rmodf, p = quo(R, f)
  @assert all(is_unit(Rmodf(x)) for x in final_gens)
  #@assert all(isone(F.p2(elem_in_algebra(x))) for x in final_gens)
  for x in final_gens
    # assert that x in final_gens is (x, e2) (modulo f2)
    # so check that the second component is = e2 mod f2
    if ii == 1
      @assert F.p2(elem_in_algebra(x)) - F.p2(F.e2) in F.f2
    else
      @assert F.p1(elem_in_algebra(x)) - F.p1(F.e1) in F.f1
    end
  end
  if !do_maximal
    if ii == 1
      F.sigma1_gens = final_gens
    else
      F.sigma2_gens = final_gens
    end
  end
  return final_gens
end
