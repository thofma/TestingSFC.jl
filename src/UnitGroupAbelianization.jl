function _compute_homomorphism(S, to_Q, to_abelian_group, f)
  return hom(S, S, [to_abelian_group(f(to_Q(g))) for g in gens(S)])
end

function unit_group_injection_into_abelian_group_automorphisms(Q)
  S, to_Q, to_abelian_group = isomorphism(FinGenAbGroup, Q)

  function to_auts(u)
    return _compute_homomorphism(S, to_Q, to_abelian_group, x -> x * u)
  end

  function to_unit(h)
    return to_Q(h(to_abelian_group(one(Q))))
  end


  return S, to_auts, to_unit
end

function unit_group_abelianization_nonrecursive(Q; use_matrices = true)
  unit_group_abelianization_nonrecursive(OscarGroup, Q; use_matrices = use_matrices)
end

abstract type UnitGroupDefault end

abstract type UnitGroupViaFiniteRings end

function unit_group_abelianization_nonrecursive(::Type{T}, Q; use_matrices = :auto) where {T}
  return _unit_group_abelianization_nonrecursive(T, Q; use_matrices = use_matrices)
end

function __dispatch_nonsense_for_magma(::Any, Q) 
  error("Magma is not available or not installed.")
end

function _unit_group_abelianization_nonrecursive_permutation_group(::Type{MagmaGroup}, Q) 
  return __dispatch_nonsense_for_magma(MagmaGroup, Q)
end

function __unit_group_abelianization_nonrecursive_permutation_group(::Any, Q) 
  U, QtoU = unit_group_quotient_raw(TestingSFC.MagmaGroup, Q; split = false)
  MHab, HtoMHab = maximal_abelian_quotient(U)
  Hab, MHabtoHab, HabtoMHab = isomorphism(FinGenAbGroup, MHab)
  fw = x -> MHabtoHab(image(HtoMHab, image(QtoU, x)))
  bw = y -> preimage(QtoU, preimage(HtoMHab, HabtoMHab(y)))
  return Hab, fw, bw
end

function _unit_group_abelianization_nonrecursive_permutation_group(::Type{OscarGroup}, Q) 
  S, to_auts, to_unit = unit_group_injection_into_abelian_group_automorphisms(Q)
  units = unit_group_generators(Q)
  A = automorphism_group(S)
  #B, BtoA = sub(A, [A(to_auts(u)) for u in units])
  @vprint :SFC "Computing permutation representation ... "
  iso = isomorphism(PermGroup, A)
  @vprintln :SFC "degree $(degree(codomain(iso)))"
  P, Ptocodomainiso = sub(codomain(iso), [iso(A(to_auts(u))) for u in units])
  Pab, PtoPab =  maximal_abelian_quotient(FinGenAbGroup, P)
  @vprintln :SFC "Abelianization: $(elementary_divisors(Pab))"

  fw = function(x)
    @assert parent(x) === Q
    PtoPab(iso(A(to_auts(x); check = false)))
  end
  bw = function(y)
    @assert parent(y) === Pab
    return to_unit(hom(preimage(iso, preimage(PtoPab, y))))
  end
  return Pab, fw, bw
end

function _unit_group_abelianization_nonrecursive(::Type{T}, Q; use_matrices = :auto) where {T}
  S, to_auts, to_unit = unit_group_injection_into_abelian_group_automorphisms(Q)
  units = unit_group_generators(Q)
  el = elementary_divisors(S)
  @vprintln :SFC "Computing unit group abelianization (using $T) for R^+ = $(el)"
  if (use_matrices == :auto && all(isequal(el[1]), el) && is_prime(el[1])) || (use_matrices isa Bool && use_matrices)
    @assert all(isequal(el[1]), el)
    @assert is_prime(el[1])
    n = ngens(S)
    p = Int(el[1])


    F = GF(p; cached = false)
    @vprintln :SFC "Computing subgroup of GL($n, $p)"
    umatgens = [F.(to_auts(u).map) for u in units]
    H = matrix_group(T, umatgens)
    MHab, HtoMHab =  maximal_abelian_quotient(H)
    if T === OscarGroup
      MHabtoHab = isomorphism(FinGenAbGroup, MHab)
      Hab = codomain(MHabtoHab)
      HabtoMHab = inv(MHabtoHab)
    else
      Hab, MHabtoHab, HabtoMHab = isomorphism(FinGenAbGroup, MHab)
    end
    A = Hab
    #A = codomain(HabtoA)
    #return A, x -> HabtoA(HtoAb(H(F.(to_auts(x).map)))), y -> to_unit(hom(S, S, matrix((preimage(HtoAb(preimage(HabtoA, y)))))))
    fw = function(x)
      return MHabtoHab(image(HtoMHab, H(F.(to_auts(x).map))))
    end

    if T === OscarGroup
      bw = function(y)
        return to_unit(hom(S, S, lift.(Ref(ZZ), matrix(preimage(HtoMHab, HabtoMHab(y))))))
      end
    else
      bw = function(y)
        return to_unit(hom(S, S, lift.(Ref(ZZ), magma_matrix_to_oscar_matrix(F, (preimage(HtoMHab, HabtoMHab(y))).x))))
      end
    end

    return A, fw, bw 
  else
    return _unit_group_abelianization_nonrecursive_permutation_group(T, Q)
  end
end

function unit_group_abelianization_unit_group_ring(::Type{T}, Q; use_matrices = true) where {T}
  O = Q.base_ring
  I = Q.ideal
  el = Q.basis_matrix
  @assert is_diagonal(el)
  el = diagonal(el)
  @assert all(isequal(el[1]), el)
  @assert is_prime(el[1])
  p = el[1]
  G = group(algebra(O))
  F = GF(p)
  FG = F[G]
  #FG, OtoFG = StructureConstantAlgebra(O, I, p)
  F = base_ring(FG)
  A, AtoFG = StructureConstantAlgebra(FG)
  Aunits = Hecke.K1(A; do_units = true)
  mats = representation_matrix.(AtoFG.(Aunits))
  A, mattoA, Atomat = magma_abelian_quotient_slow_of_matrix_group(mats)
  fw = function(u)
    m = representation_matrix(FG(F.(u.elem.coordinates)))
    return mattoA(m)
  end
  bw = function(a)
    m = Atomat(a)
    b = FG(one(FG).coeffs * m)
    @assert representation_matrix(b) == m
    return Q(O(lift.(Ref(ZZ), b.coeffs)))
  end
  A, fw, bw
end

function unit_group_abelianization(::Type{T}, Q; use_matrices = :auto, split = true, special = false) where {T}
  O = Q.base_ring
  F = Q.ideal
  if !split || special
    if !special
      return unit_group_abelianization_nonrecursive(T, Q; use_matrices = use_matrices)
    else
      return unit_group_abelianization_unit_group_ring(T, Q; use_matrices = use_matrices)
    end
  end
  moduli = _compute_a_complete_coprime_splitting(O, F, split = true)
  quorings = []
  maps = []
  for m in moduli
    QQ, OtoQQ = quo(O, m * O)
    push!(quorings, (QQ, OtoQQ))
    A, f, g = unit_group_abelianization_nonrecursive(T, QQ; use_matrices = use_matrices)
    for a in gens(A)
      @assert is_unit(g(a))
    end
    push!(maps, (A, f, g))
  end

  AA, projs, injs = biproduct(first.(maps)...)

  function fw(x)
    sum([injs[i](maps[i][2](quorings[i][1](x.elem))) for i in 1:length(quorings)])
  end

  function bw(y)
    els = [ (maps[i][3](projs[i](y))).elem for i in 1:length(quorings)]
    return Q(crt(els, moduli))
  end
  return AA, fw, bw
end




