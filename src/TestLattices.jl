################################################################################
#
#  Creation
#
################################################################################

# Mainly for debugging purposes
function _test_lattice(O::Hecke.AlgAssAbsOrd, beta, f)
  b = elem_in_algebra(beta)
  binv = inv(b)
  primes = prime_divisors(numerator(det(Hecke.basis_matrix_wrt(f, O))))
  Y = binv * O
  X = lattice_with_local_conditions(O, primes, [Y for i in 1:length(primes)])
  I = b * X
  M = parent(beta)
  return I
end

################################################################################
#
#  Stable freeness test
#
################################################################################

function _defines_stably_free_test_lattice(beta::Hecke.AlgAssAbsOrdElem, O, f, side = :right; GRH::Bool = true)
  M = parent(beta)
  # compute ray class group
  OC, mC, OCtoR, RtoRquo = get_attribute!(O, :ray_class_group_stuff) do
    compute_ray_class_group(O, f; GRH = GRH)
  end
  Z, ZtoA = center(algebra(M))

  normbeta = OC(Hecke.normred_over_center(elem_in_algebra(beta), ZtoA))
  return is_zero(RtoRquo(OCtoR\(normbeta*OC)))
end

################################################################################
#
#  Freeness test
#
################################################################################

function _defines_free_test_lattice(beta::Hecke.AlgAssAbsOrdElem, O; side = :right, GRH::Bool = true, fiber_product = nothing, proof = :rigorous)
  # f = two-sided ideal
  if fiber_product == nothing
    # fibre product needs to have the same maximal order
    _F = fiber_product_from_eichler_splitting(O, parent(beta))
  else
    _F = fiber_product
  end
  @assert _F.M == parent(beta)
  fl = _s1_method(O, elem_in_algebra(beta), _F, s1_method = :heuristic, GRH = GRH)
  if fl || proof == :heuristic
    return fl
  else
    return _s1_method(O, elem_in_algebra(beta), _F, s1_method = :rigorous, GRH = GRH)
  end
end
