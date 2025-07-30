function idempotent_for_canonical_quotient(A)
  return idempotent_for_commutative_components(A) + idempotent_for_quaternionic_noneichler_components(A)
end

function canonical_quotient_algebra(A)
  @vprintln :SFC 1 "Computing idempotents for abelian part"
  e = idempotent_for_commutative_components(A)
  @vprintln :SFC 1 "Computing idempotents for quaternionic part"
  ee = idempotent_for_quaternionic_noneichler_components(A)
  e = e + ee
  @vprintln :SFC 1 "Construct the quotient algebra"
  B, BtoA = Hecke._subalgebra(A, e, true)
  proj = elem_type(B)[]
  @vprintln :SFC 1 "Construct the projection"
  for a in basis(A)
    prim = preimage(BtoA, a * e)
    push!(proj, prim)
  end
  return B, hom(A, B, proj)
end

function canonical_quotient_order(Gamma)
  A = algebra(Gamma)
  B, BtoA = canonical_quotient_algebra(A)
  return BtoA(Gamma)
end

function idempotent_for_commutative_components(A)
  G = group(A)
  H, mH = derived_subgroup(G)
  eH = 1//order(H) * sum(A(mH(h)) for h in H)
  return eH
end

function idempotent_for_quaternionic_noneichler_components(A)
  G = group(A)
  X = character_table(G)
  AA, = abelian_closure(QQ)
  AAG = AA[G] 
  quats = [ x for x in X if indicator(x) == -1 && degree(x) == 2]
  z = zero(AAG)
  for x in quats
    e = central_primitive_idempotent(AAG, x)
    z += e
  end
  c = Hecke.coefficients(z, copy = false)
  return sum(QQ(c[AAG.group_to_base[g]]) * A(g) for g in G)
end

function central_primitive_idempotent(AAG, chi)
  G = group(AAG)
  AA = base_ring(AAG)
  n = order(G)
  return degree(chi) * AA(1//n) * sum(chi(inv(g)) * AAG(g) for g in G)
end
