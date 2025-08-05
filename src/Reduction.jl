function lift_unit_from_to(x, Q1, Q2)
  # assumes that Q2 ->> Q1, inducing a surjection (Q2)^* -> (Q1)^*
  @assert parent(x) == Q1
  f1 = Q1.ideal
  xlift = Q2(x.elem)
  @assert is_unit(Q1(x.elem))
  b = basis(f1, copy = false)
  k = 0
  while !is_unit(xlift)
    if k > 2000
      error("Too many tries when lifting unit")
    end
    k += 1
    xlift = Q2(x.elem + Q1.base_ring(sum(rand(-10:10) * b[i] for i in 1:length(b))))
  end
  @assert is_unit(xlift)
  return xlift
end

function from_quotient_to_center(F, OC, mC, RtoRquo, OCtoR, Rmodf2)
  return y -> begin
    _beta = y
    _betaf2 = _beta
    _beta = _beta.elem
    @assert has_preimage_with_preimage(F.p2, elem_in_algebra(_beta))[1]
    __beta = F.e2 * has_preimage_with_preimage(F.p2, elem_in_algebra(_beta))[2]
    beta = (F.M)(F.e1 + __beta)
    @assert !is_zero(norm(elem_in_algebra(beta)))
    @assert is_one(F.p1(elem_in_algebra(beta)))
    @assert Rmodf2(F.R2(F.p2(elem_in_algebra(beta)))) == _betaf2
    normbeta = OC(Hecke.normred_over_center(elem_in_algebra(beta), mC))
    return normbeta
  end
end

function partial_kernel_generators(::Type{T}, F; use_matrices = :auto, GRH::Bool = true, special = false) where {T}
  h2 = TestingSFC.h2(F)
  f2 = F.f2
  R2 = F.R2
  @vprintln :SFC "Computing R2/h2 and R2/f2"
  Rmodh2, = quo(F.R2, h2 * F.R2)
  Rmodf2, = quo(F.R2, f2 * F.R2)
  @vprintln :SFC "Computing abelianization of (R2/h2)^*"
  @vtime :SFC 2 Rmodh2ab, Rmodh2toRmodh2ab, Rmodh2abtoRmodh2 = unit_group_abelianization(T, Rmodh2; use_matrices = use_matrices, special = special)
  @vprintln :SFC "Abelianization is: $(elementary_divisors(Rmodh2ab))"
  @vprintln :SFC "Computing ray class group (OC^+/g)^*/nr"
  # compute ray class group
  OC, mC, OCtoR, RtoRquo = compute_ray_class_group(F.R, F.f; GRH = GRH)
  M = F.M
  map_to_center = from_quotient_to_center(F, OC, mC, RtoRquo, OCtoR, Rmodf2)

  @vprintln :SFC "Setting up ∂"
  imgs = FinGenAbGroupElem[]
  for g in gens(Rmodh2ab)
    # Mapping g
    @assert is_unit(Rmodh2abtoRmodh2(g))
    _beta = lift_unit_from_to(Rmodh2abtoRmodh2(g), Rmodh2, Rmodf2)
    normbeta = map_to_center(_beta)
    push!(imgs, RtoRquo(OCtoR\(normbeta*OC)))
  end
  partial = hom(Rmodh2ab, codomain(RtoRquo), imgs)
  @vprintln :SFC "Computing ker(∂)"
  K, KtoRmodh2ab = kernel(partial, false)
  S, StoK = snf(K)
  Rmodh2, Rmodf2, [ Rmodh2abtoRmodh2(KtoRmodh2ab(StoK(s))) for s in gens(S)]
end

function reduction(F; use_matrices = :auto, GRH::Bool = true)
  return reduction(OscarGroup, F; use_matrices, GRH = GRH)
end

function reduction(::Type{T}, F; use_matrices = :auto, GRH::Bool = true, special = false) where {T}
  if !is_eichler(algebra(F.R1))
    if !is_eichler(algebra(F.R2))
      error("one of the two projections must be Eichler")
    end
    F = swap(F)
  end
  @assert is_eichler(algebra(F.R1))
  R2 = F.R2
  R1 = F.R1
  R = F.R
  h2 = TestingSFC.h2(F)

  @vprintln :SFC "Computing kernel of ∂"
  @v_do :SFC pushindent()
  @vtime :SFC 2 Rmodh2, Rmodf2, K = partial_kernel_generators(T, F; use_matrices, GRH = GRH, special)
  @v_do :SFC popindent()
  @vprintln :SFC "ker(∂) number of generators: $(length(K))"
  # Computing Eichler splitting fiber product for the freeness test
  @vprintln :SFC "Computing Eichler splitting for improved PIP test"
  @v_do :SFC pushindent()
  @vtime :SFC 2 _F = fiber_product_from_eichler_splitting(R, F.M)
  @v_do :SFC popindent()
  n = length(K)
  @vprintln :SFC "Testing freeness of $(length(K)) stably free test lattices"
  @v_do :SFC pushindent()
  @vtime :SFC 2 for i in 1:n
    o = K[i]
    _beta = lift_unit_from_to(o, Rmodh2, Rmodf2).elem
    __beta = F.e2 * has_preimage_with_preimage(F.p2, elem_in_algebra(_beta))[2]
    beta = (F.M)(F.e1 + __beta)
    @vprint :SFC 3 "Checking stable freeness of test lattice:"
    fl = _defines_stably_free_test_lattice(beta, R, F.f; GRH = GRH)
    @vprintln :SFC 3 " $(fl)"

    if !fl
      continue
    end

    @vprintln :SFC 3 "Checking freeness of test lattice"
    fl = _defines_free_test_lattice(beta, R; GRH = GRH, fiber_product = _F)
    @vprintln :SFC 3 " $(fl)"
    if !fl
      @v_do :SFC popindent()
      return false
    end
  end
  @v_do :SFC popindent()
  return true
end

function proof_via_standard_eichler_splitting(R; use_matrices = false, GRH::Bool = true)
  return proof_via_standard_eichler_splitting(OscarGroup, R; use_matrices, GRH = GRH)
end

function proof_via_standard_eichler_splitting(::Type{T}, R; use_matrices = false, GRH::Bool = true) where {T}
  @vprintln :SFC "Computing fiber product"
  F = TestingSFC.fiber_product_from_eichler_splitting(R)
  RR = F.R2
  @vprintln :SFC "Checking SFC property for non-Eichler part"
  @v_do :SFC pushindent()
  @vtime :SFC 2 fl = has_stably_free_cancellation_naive(RR; GRH = GRH)
  @v_do :SFC popindent()
  @vprintln :SFC "non-Eichler projection does have SFC: $(fl)"
  if !fl
    return false
  end
  @vtime :SFC 2 return reduction(T, F; use_matrices, GRH = GRH)
end
