function has_not_stably_free_cancellation_probably_no_split(O::Hecke.AlgAssAbsOrd; repetitions::Int = 50, GRH = false)
  @vprintln :SFC 1 "Testing $repetitions random stably free test lattices"
  M = maximal_order(O)
  f = Hecke._get_a_twosided_conductor(O, M)
  fl, f = is_locally_radical_with_adjustment(M, f)
  unitgens = Hecke.K1_order_mod_conductor(M, M, f * M; do_units = true)
  Q, = quo(M, f * M)
  i = 0
  k = 0
  units = 0
  stably_free = 0
  free = 0
  S = Set()
  while i <= repetitions
    k += 1
    if k >= 100000
      error("Something odd")
    end
    if rand() < 0.5
      beta = rand(M, -10:10)
    else
      beta = one(M)
      if length(unitgens) != 0
        for j in 1:rand(1:length(unitgens))
          beta = beta * rand(unitgens)
        end
      end
    end
    if !is_unit(Q(beta))
      continue
    end
    units += 1

    #@vprintln :SFC 1 "Constructing Swan module"
    #I = _test_lattice(O, beta)
    #@vprintln :SFC 1 "Done"

    if !_defines_stably_free_test_lattice(beta, O, f; GRH = GRH)
      continue
    end
    stably_free += 1

    # so X_beta is stably free
    #@vprintln :SFC 1 "Constructing Swan module"
    #I = _test_lattice(O, beta, f)
    #@assert I * M == beta * M

    #@assert Hecke._test_ideal_sidedness(I, O, :right)

    #I.order = O

    #@vprintln :SFC 1 "Testing principality"
    #if !Hecke.__isprincipal(Gamma2, I * Gamma2, :right, beta)[1]
    I = _test_lattice(O, beta, f)
    #fl, _ = Hecke.__isprincipal(O, I * O, :right, beta; GRH = GRH); 
    fl, = Hecke._is_principal_with_data_bj(I * O, O, side = :right, _alpha = beta, GRH = GRH)

    if !fl #!Hecke.__isprincipal(O, I, :right, beta)[1]
      @vprintln :SFC 1 "Order does not have SFC"
      @vprintln :SFC 1 "Tried the following number elements: $k"
      return true, beta, f
    end
    i += 1
    free += 1
    push!(S, elem_in_algebra(beta))
    #println("i: $i\nfree: $free")
  end
  @vprintln :SFC 1 "Tried the following number elements: $k"
  @vprintln :SFC 1 "Number of test lattices: $units"
  @vprintln :SFC 1 "Stably free: $stably_free"
  @vprintln :SFC 1 "Free: $free"
  @vprintln :SFC 1 "Unique elements: $(length(S))"
  @vprintln :SFC 1 "Order probably has SFC"
  return false
end

function has_not_stably_free_cancellation_probably(O::Hecke.AlgAssAbsOrd; repetitions::Int = 50, s1_method = :rigorous, GRH::Bool = false)
  @vprintln :SFC 1 "Testing $repetitions random stably free test lattices"
  #@vprintln :SFC 1 "GRH $(GRH)"
  #Gamma2 = Hecke._ring_of_multipliers_integral_ideal(pradical(O, 2), fmpz(2))
  #@show valuation(discriminant(Gamma2), 2)
  #I = pradical(Gamma2, 2)
  ##for i in 1:3
  #  max_id = Hecke._maximal_ideals(Gamma2, I, 2, strict_containment = true)
  #  for m in max_id
  #    @vtime :AlgAssOrd 1 Gamma22 = Hecke._ring_of_multipliers_integral_ideal(m, fmpz(2))
  #    Gamma2 += Gamma22
  #    @show valuation(discriminant(Gamma2), 2)
  #  end
  #  @show valuation(discriminant(Gamma2), 2)
  ##end
  #M = maximal_order(Gamma2)
  if is_commutative(algebra(O))
    @vprintln :SFC 1 "Algebra is commutative ..."
    @vprintln :SFC 1 "Order does have SFC"
    return false
  end

  # If there is no splitting, do something else
  de = decompose(algebra(O))
  eich = [is_eichler(Hecke._as_algebra_over_center(d[1])[1]) for d in de]

  @vprintln :SFC 1 "Eichler components $(eich)"

  if all(eich)
    @vprintln :SFC 1 "Algebra is Eichler ..."
    @vprintln :SFC 1 "Order does have SFC"
    return false
  end

  @vprintln :SFC 1 "Computing fiber product (from Eichler splitting)"
  if all(eich) || all((!).(eich))
    @vprintln :SFC 1 "No splitting ..."
    return has_not_stably_free_cancellation_probably_no_split(O; repetitions, GRH = GRH)
  end
  Fprod = fiber_product_from_eichler_splitting(O)
  M = Fprod.M
  #Fl = conductor(O, M, :right)
  #_F = prod(Hecke.support(norm(Fl * M)))
  #F = _F * M
  #@assert F * M == F
  #Q, = quo(M, F * M)
  f = Fprod.f
  F = f
  #unitgens = Hecke.K1_order_mod_conductor(M, M, F, do_units = true)
  f2copy = Fprod.f2 * Fprod.M2
  unitgens = Hecke.K1_order_mod_conductor(Fprod.M2, Fprod.M2, f2copy, do_units = true)
  #@vprintln :SFC 1 "#units = $(length(unitgens))"
  Q, = quo(M, F * M)
  #@vprintln :SFC 1 "Computing locally free class group"
  #C, mC = locally_free_class_group_with_disc_log(O)
  if ismaximal(O)
    error("Order must not be maximal")
  end
  i = 0
  k = 0
  units = 0
  stably_free = 0
  free = 0
  S = Set()
  while i <= repetitions
    k += 1
    if k >= 1000000
      error("Something odd")
    end
    if rand() < 0.5
      beta = rand(M, -10:10)
      while !is_invertible(elem_in_algebra(beta))[1]
        beta = rand(M, -10:10)
      end
    else
      beta = one(Fprod.M2)
      if length(unitgens) != 0
        for j in 1:rand(1:length(unitgens))
          beta = beta * rand(unitgens)
        end
      end
      beta = Fprod.e2 * haspreimage(Fprod.p2, elem_in_algebra(beta))[2]
      beta = M(Fprod.e1 + beta)
      #bb = rand(1:_F)
      #while !isone(gcd(_F, bb))
      #  bb = rand(1:_F)
      #end
      #beta = M(sum(rand(-10:10) * b for b in basis(F)) + bb * one(algebra(M)))
    end
    if !is_unit(Q(beta))
      continue
    end
    units += 1

    #@vprintln :SFC 1 "Constructing Swan module"
    #I = _test_lattice(O, beta)
    #@vprintln :SFC 1 "Done"

    if !_defines_stably_free_test_lattice(beta, O, F; GRH = GRH)
      continue
    end
    stably_free += 1

    # so X_beta is stably free
    #@vprintln :SFC 3 "Constructing Swan module"
    #I = _test_lattice(O, beta)
    #@assert I * M == beta * M

    #@assert Hecke._test_ideal_sidedness(I, O, :right)

    #I.order = O

    #@vprintln :SFC 3 "Testing principality"
    #if !Hecke.__isprincipal(Gamma2, I * Gamma2, :right, beta)[1]
    fl = _s1_method(O, elem_in_algebra(beta), Fprod, s1_method = s1_method; GRH = GRH)
    if !fl #!Hecke.__isprincipal(O, I, :right, beta)[1]
      @vprintln :SFC 3 "Order does not have SFC"
      @vprintln :SFC 3 "Tried the following number elements: $k"
      return true, beta, f
    end
    i += 1
    free += 1
    push!(S, elem_in_algebra(beta))
    #println("i: $i\nfree: $free")
  end
  @vprintln :SFC 3 "Tried the following number elements: $k"
  @vprintln :SFC 3 "Number of Generalized test lattice: $units"
  @vprintln :SFC 3 "Stably free: $stably_free"
  @vprintln :SFC 3 "Free: $free"
  @vprintln :SFC 3 "Unique elements: $(length(S))"
  @vprintln :SFC 3 "Order probably has SFC"
  return false
end

################################################################################
#
#  More complicated algorithm of Werner
#
################################################################################

function sfc_of_canonical_quotient(Gamma; GRH::Bool = false, method = :s1)
  GammaGamma = canonical_quotient_order(Gamma)
  @vprintln :SFC 1 "Degree of quotient: $(degree(GammaGamma))"
  #@vprintln :SFC 1 "GRH: $GRH"
  if method === :s1
    fl, = has_not_stably_free_cancellation_probably(GammaGamma; repetitions = 100, GRH = GRH, s1_method = :rigorous)
  else
    @assert method === :bj
    fl, = has_not_stably_free_cancellation_probably_no_split(GammaGamma; repetitions = 100, GRH = GRH)
  end
  @vprintln :SFC 1 "Found a stably free non-free test lattice: $fl"
  if fl
    @vprintln :SFC 1 "Image of projection onto abelian and quaternionic components does not have SFC"
    return false
  else
    @vprintln :SFC 1 "Image of projection onto abelian and quaternionic components probably has SFC"
    return true
    @vprintln :SFC 1 "Now proof that quotient has SFC"
    return proof_via_standard_eichler_splitting_new(Gamma; GRH = GRH)
  end
end


