function has_stably_free_cancellation_naive(Lambda; GRH = true)
  # This is Algorithm 8.9
  return has_stably_free_cancellation_naive(OscarGroup, Lambda; GRH = GRH)
end

function has_stably_free_cancellation_naive(::Type{TT}, Lambda; GRH::Bool = true) where {TT}
  @vprintln :SFC "Naive SFC check for order of degree: $(degree(Lambda))"
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
  fl, f = is_locally_radical_with_adjustment(ML, f)
  @assert f * ML == f
  Q, = quo(ML, f * ML);
  @vprintln :SFC "Abelian structure of quotient ring M/f: $(filter(!is_one, elementary_divisors(Q.basis_matrix)))"
  @vprintln :SFC "Computing unit group (M/f)^*"
  SS, QtoSS = unit_group_quotient(TT, Q)
  @assert f * Lambda == f
  @vprintln :SFC "Computing unit group (Λ/f)^*"
  lambdamodf, = quo(Lambda, f * Lambda)
  #@info "Computing unit group generators of (R/f)^*"
  lambdamodfgens = unit_group_generators(lambdamodf)
  @vprintln :SFC "Mapping to (M/f)^* and constructing (Λ/f)^* <= (M/f)^*"
  lambdamofgensinMmodf = [image(QtoSS, Q(ML(elem_in_algebra(a.elem)))) for a in unit_group_generators(lambdamodf)]
  lambdamodfgens = sub(SS, lambdamofgensinMmodf)
  @vprintln :SFC "Computing generators of unit group M^*"
  T = Hecke._unit_group_generators_maximal(ML; GRH = GRH)
  @vprintln :SFC "Mapping to (M/f)^* and constructing M^* <= (M/f)^*"
  TinMmodf = [image(QtoSS, Q(ML(a))) for a in T]
  Tmodfgens = sub(SS, TinMmodf)
  #@info order(lambdamodfgens[1])
  #@info order(Tmodfgens[1])
  @vprintln :SFC "Computing representatives for double cosets (Λ/f)^*\\(M/f)^*/M^*"
  betas = double_coset_representatives(SS, lambdamodfgens[1], Tmodfgens[1])
  @vprintln :SFC "Number of double cosets: $(length(betas))"
  @vprintln :SFC "Checking all test lattices"
  @v_do :SFC 2 pushindent()
  for i in 1:length(betas)
    @vprintln :SFC 2 "Testing $i/$(length(betas))"
    el = preimage(QtoSS, betas[i]).elem
    fl = is_invertible(elem_in_algebra(el))[1]
    while !fl
      el = betas[i].elem + ML(rand(f, 5))
      fl = is_invertible(elem_in_algebra(el))[1] && is_invertible(Q(el))[1]
    end
    @assert Q(el) == preimage(QtoSS, betas[i])
    @vprint :SFC 2 "Testing if test lattice is stably free ..."
    _fl =  _defines_stably_free_test_lattice(el, Lambda, f, :right; GRH = GRH)
    @vprintln :SFC 2 " $(_fl)"
    if _fl
      I = _test_lattice(Lambda, el, f)
      @vprint :SFC 2 "Testing if test lattice is free ..."
      fl, bb = Hecke._is_principal_with_data_bj(I * Lambda, Lambda, side = :right, _alpha = el, GRH = GRH)
      @vprintln :SFC 2 " $(fl)"
      if fl
        @assert bb * Lambda == I
      else
        @vprintln :SFC "Found stably free non-free test lattice; Λ does not have SFC."
        @v_do :SFC 2 popindent()
        return false
      end
    else
      @vprintln :SFC 2 "Test lattice not stably free"
    end
  end
  @v_do :SFC 2 popindent()
  return true
end
