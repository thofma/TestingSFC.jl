module FiniteRingsExtension

using TestingSFC, Oscar, FiniteRings

TestingSFC._default_group_type(::Bool) = TestingSFC.UnitGroupViaFiniteRings

function TestingSFC._unit_group_abelianization_nonrecursive(::Type{TestingSFC.UnitGroupViaFiniteRings}, Q; use_matrices = true)
  R, RtoQ = finite_ring(Q)
  Ab, m = FiniteRings.abelianization_of_unit_group(R)
  return Ab, x -> m(Oscar.preimage(RtoQ, x)), y -> RtoQ(Oscar.preimage(m, y))
end

end
