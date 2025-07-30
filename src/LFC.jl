function has_LFC(::Type{TT}, Lambda; GRH::Bool = true) where {TT}
  @vprintln :SFC "LFC check for order of degree: $(degree(Lambda))"
  @vprintln :SFC "Representation for unit groups of finite rings: $(TT)"
  ML = maximal_order(Lambda)
  @vprintln :SFC "Computing two-sided conductor ..."
  f = Hecke._get_a_twosided_conductor(Lambda, ML)
  A = algebra(ML)
  Q, = quo(ML, f * ML)
  if is_one(abs(det(Q.basis_matrix)))
    @vprintln :SFC "Conductor is trivial, order is maximal, so has SFC"
    return true
  end
  @vprintln :SFC "Possible adjustment for conductor to be locally radical"
  fl, f = TestingSFC.is_locally_radical_with_adjustment(ML, f)
  @assert f * ML == f
  Q, = quo(ML, f * ML);
  @vprintln :SFC "Abelian structure of quotient ring M/f: $(filter(!is_one, elementary_divisors(Q.basis_matrix)))"
  @vprintln :SFC "Computing unit group (M/f)^*"
  # SS, QtoSS = TestingSFC.unit_group_quotient(TT, Q)
  # @assert f * Lambda == f
  # @vprintln :SFC "Computing unit group (Λ/f)^*"
  # lambdamodf, = quo(Lambda, f * Lambda)
  # #@info "Computing unit group generators of (R/f)^*"
  # lambdamodfgens = TestingSFC.unit_group_generators(lambdamodf)
  # @vprintln :SFC "Mapping to (M/f)^* and constructing (Λ/f)^* <= (M/f)^*"
  # lambdamofgensinMmodf = [image(QtoSS, Q(ML(elem_in_algebra(a.elem)))) for a in unit_group_generators(lambdamodf)]
  # lambdamodfgens = sub(SS, lambdamofgensinMmodf)
  # @vprintln :SFC "Computing generators of unit group M^*"
  # T = Hecke._unit_group_generators_maximal(ML; GRH = GRH)
  # @vprintln :SFC "Mapping to (M/f)^* and constructing M^* <= (M/f)^*"
  # TinMmodf = [image(QtoSS, Q(ML(a))) for a in T]
  # Tmodfgens = sub(SS, TinMmodf)
  # #@info order(lambdamodfgens[1])
  # #@info order(Tmodfgens[1])
  # @vprintln :SFC "Computing representatives for double cosets (Λ/f)^*\\(M/f)^*/M^*"
  # betas = double_coset_representatives(SS, lambdamodfgens[1], Tmodfgens[1])
  # @vprintln :SFC "Number of double cosets: $(length(betas))"
  # @vprintln :SFC "Checking all test lattices"
  # @v_do :SFC 2 pushindent()
  S, StoQ, QtoS = isomorphism(Hecke.FinGenAbGroup, Q)
  @info "computing unitgens"
  unitgens = TestingSFC.unit_group_generators(Q)
  for i in 1:10
    @info i
    @info "constructing unit"
    if false rand() < 0.5
      beta = Q(rand(ML, -10:10))
      if !is_unit(Q(beta))
        continue
      end
    else
      @info "asds"
      beta = one(Q)
      if length(unitgens) != 0
        for j in 1:rand(1:length(unitgens))
          beta = beta * rand(unitgens)
        end
      end
    end
    @info "done"
    #@vprintln :SFC 2 "Testing $i/$(length(betas))"
    #el = preimage(QtoSS, betas[i]).elem
    el = beta.elem
    fl = is_invertible(elem_in_algebra(el))[1]
    @info "adjusting"
    while !fl
      @info "still adjusting"
      el = beta.elem + ML(rand(f, 5))
      fl = is_invertible(elem_in_algebra(el))[1] && is_invertible(Q(el))[1]
    end
    @info "done"
    @assert Q(el) == beta
    @info "computing test lattice"
    I = TestingSFC._test_lattice(Lambda, el, f)
    @info "done"
    ORI = right_order(I)
    Main.ORI = ORI
    error("asd")
    fl = TestingSFC.proof_via_standard_eichler_splitting(TestingSFC.UnitGroupViaFiniteRings, ORI, GRH = true)
    if !fl
      @v_do :SFC 2 popindent()
      return false
    end
  end
  @v_do :SFC 2 popindent()
  return true
end

function has_LFC_eichler_splitting(::Type{T}, R; GRH::Bool = true) where {T}
  F = TestingSFC.fiber_product_from_eichler_splitting(R)
  h2 = TestingSFC.h2(F)
  f2 = F.f2
  R2 = F.R2
  fl, _ = TestingSFC.is_locally_radical_with_adjustment(F.M, F.f)
  @assert fl
  @vprintln :SFC "Computing R2/h2 and R2/f2"
  Rmodh2, = quo(F.R2, h2 * F.R2)
  Rmodf2, = quo(F.R2, f2 * F.R2)
  @vprintln :SFC "Computing abelianization of (R2/h2)^*"
  Rmodh2ab, Rmodh2toRmodh2ab, Rmodh2abtoRmodh2 = TestingSFC.unit_group_abelianization(T, Rmodh2)
  M = F.M
  @vprintln :SFC "(Lambdabar)^*^ab: $(elementary_divisors(Rmodh2ab)) (order $(order(Rmodh2ab)))"
  imgs = FinGenAbGroupElem[]
  for g in Rmodh2ab
    # Mapping g
    @assert is_unit(Rmodh2abtoRmodh2(g))
    _beta = TestingSFC.lift_unit_from_to(Rmodh2abtoRmodh2(g), Rmodh2, Rmodf2).elem
    __beta = F.e2 * haspreimage(F.p2, elem_in_algebra(_beta))[2]
    beta = (F.M)(F.e1 + __beta)
    I = TestingSFC._test_lattice(R, beta, F.f)
    ORI = right_order(I)
    fl = TestingSFC.proof_via_standard_eichler_splitting(ORI, GRH = true)
    if !fl
      return false
    end
  end
  return true

  @vprintln :SFC "LFC check for order of degree: $(degree(Lambda))"
  @vprintln :SFC "Representation for unit groups of finite rings: $(TT)"
  ML = maximal_order(Lambda)
  @vprintln :SFC "Computing two-sided conductor ..."
  f = Hecke._get_a_twosided_conductor(Lambda, ML)
  A = algebra(ML)
  Q, = quo(ML, f * ML)
  if is_one(abs(det(Q.basis_matrix)))
    @vprintln :SFC "Conductor is trivial, order is maximal, so has SFC"
    return true
  end
  @vprintln :SFC "Possible adjustment for conductor to be locally radical"
  fl, f = TestingSFC.is_locally_radical_with_adjustment(ML, f)
  @assert f * ML == f
  Q, = quo(ML, f * ML);
  @vprintln :SFC "Abelian structure of quotient ring M/f: $(filter(!is_one, elementary_divisors(Q.basis_matrix)))"
  @vprintln :SFC "Computing unit group (M/f)^*"
  # SS, QtoSS = TestingSFC.unit_group_quotient(TT, Q)
  # @assert f * Lambda == f
  # @vprintln :SFC "Computing unit group (Λ/f)^*"
  # lambdamodf, = quo(Lambda, f * Lambda)
  # #@info "Computing unit group generators of (R/f)^*"
  # lambdamodfgens = TestingSFC.unit_group_generators(lambdamodf)
  # @vprintln :SFC "Mapping to (M/f)^* and constructing (Λ/f)^* <= (M/f)^*"
  # lambdamofgensinMmodf = [image(QtoSS, Q(ML(elem_in_algebra(a.elem)))) for a in unit_group_generators(lambdamodf)]
  # lambdamodfgens = sub(SS, lambdamofgensinMmodf)
  # @vprintln :SFC "Computing generators of unit group M^*"
  # T = Hecke._unit_group_generators_maximal(ML; GRH = GRH)
  # @vprintln :SFC "Mapping to (M/f)^* and constructing M^* <= (M/f)^*"
  # TinMmodf = [image(QtoSS, Q(ML(a))) for a in T]
  # Tmodfgens = sub(SS, TinMmodf)
  # #@info order(lambdamodfgens[1])
  # #@info order(Tmodfgens[1])
  # @vprintln :SFC "Computing representatives for double cosets (Λ/f)^*\\(M/f)^*/M^*"
  # betas = double_coset_representatives(SS, lambdamodfgens[1], Tmodfgens[1])
  # @vprintln :SFC "Number of double cosets: $(length(betas))"
  # @vprintln :SFC "Checking all test lattices"
  # @v_do :SFC 2 pushindent()
  S, StoQ, QtoS = isomorphism(Hecke.FinGenAbGroup, Q)
  @info "computing unitgens"
  unitgens = Hecke.K1_order_mod_conductor(M, M, f * M; do_units = true)
  for i in 1:10
    @info i
    @info "constructing unit"
    if false rand() < 0.5
      beta = Q(rand(M, -10:10))
      if !is_unit(Q(beta))
        continue
      end
    else
      @info "asds"
      beta = one(M)
      if length(unitgens) != 0
        for j in 1:rand(1:length(unitgens))
          beta = beta * rand(unitgens)
        end
      end
      beta = Q(beta)
    end
    @info "done"
    #beta = StoQ(rand(S))
    #while !is_unit(beta)
    #  beta = StoQ(rand(S))
    #end
    #@vprintln :SFC 2 "Testing $i/$(length(betas))"
    #el = preimage(QtoSS, betas[i]).elem
    el = beta.elem
    fl = is_invertible(elem_in_algebra(el))[1]
    while !fl
      @info "ooo"
      el = beta.elem + ML(rand(f, 1))
      fl = is_invertible(elem_in_algebra(el))[1] && is_invertible(Q(el))[1]
    end
    @info "sooo"
    @assert Q(el) == beta
    I = TestingSFC._test_lattice(Lambda, el, f)
    ORI = right_order(I)
    Main.ORI = ORI
    error(asds)
    fl = TestingSFC.proof_via_standard_eichler_splitting(ORI, GRH = true)
    @info fl
  end
  @v_do :SFC 2 popindent()
  return true
end

function henri_order(Lambda)
  M = maximal_order(Lambda)
  f = TestingSFC._get_a_twosided_conductor(Lambda, M)
  A = algebra(Lambda)
  Lambdaf = order(A, ZZ, push!(basis(f), one(A)))
  return Lambdaf, f
end
