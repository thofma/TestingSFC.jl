module MagmaExtension

using TestingSFC, MagmaGroups, TestingSFC.Oscar, MagmaGroups.MagmaCall

TestingSFC.abelian_group_type(::Type{TestingSFC.MagmaGroup}) = MagmaGroups.MagmaFinGenAbGroup

TestingSFC.abelian_group_aut_type(::Type{TestingSFC.MagmaGroup}) = MagmaGroups.MagmaFinGenAbGroupAutGrp

TestingSFC.perm_group_type(::Type{TestingSFC.MagmaGroup}) = MagmaGroups.MagmaPermGroup

TestingSFC.group_map_type(::Type{TestingSFC.MagmaGroup}, ::Type{A}, ::Type{B}) where {A, B} = TestingSFC.MagmaMap{A, B}

Oscar.abelian_group(::Type{TestingSFC.MagmaGroup}, x...; kw...) = Oscar.abelian_group(MagmaGroups.Magma, x...; kw...)

Oscar.matrix_group(::Type{TestingSFC.MagmaGroup}, x...; kw...) = Oscar.matrix_group(MagmaGroups.Magma, x...; kw...)

Oscar.maximal_abelian_quotient(::Type{TestingSFC.MagmaGroup}, x...; kw...) = Oscar.maximal_abelian_quotient(x...; kw...)

TestingSFC.MagmaGroup(A::FinGenAbGroup) = MagmaGroups.MagmaGroup(A)

TestingSFC.double_coset_representatives(G::MagmaGroups.MagmaGroup, H, K) = MagmaGroups.double_coset_representatives(G, H, K)

Oscar.elementary_divisors(x::MagmaGroups.MagmaFinGenAbGroup) = Int.(magconvert(Vector{BigInt}, mag"InvariantFactors($(MagmaGroups.data(x)))"))

function __init__()
  magma_file = joinpath(@__DIR__, "..", "magma", "support.m")
  @info "Loading $(magma_file)"
  if !isfile(magma_file)
    error("File not found")
  end
  println(MagmaCall.PROC[], "Attach(\"$(magma_file)\");");
end

TestingSFC.mcall(::Bool) = true

function TestingSFC.oscar_matrix_to_magma_matrix(F, m)
  n = nrows(m)
  _m = map(x -> BigInt(lift(ZZ, x)), Oscar.Hecke._eltseq(m))
  v = magf.Matrix(F, n, n, _m)
  #v = mag"Matrix($F, $n, $n, $(_m))" 
  return v
end

function TestingSFC.magma_matrix_group(v::Vector)
  p = Int.(characteristic(base_ring(v[1])))
  F = magf.GF(p)
  G = magf.GL(nrows(v[1]), F)
  #@info "Translating matrices to Magma"
  #vv = [TestingSFC.oscar_matrix_to_magma_matrix(F, m) for m in v]
  vv = magseq()
  for m in v
    magp1.Append(vv, TestingSFC.oscar_matrix_to_magma_matrix(F, m))
  end
  #@info "Creating group"
  mS = mag"S, mS := sub<$G | $vv>; return mS";
  #@info "done"
  S = mag"Domain($mS)"
  return S, mS, F
end

function TestingSFC.magma_matrix_to_oscar_matrix(F, m)
  v = mag"[Integers()!x : x in Eltseq($m)]" 
  n = magi.Nrows(m)
  return matrix(F, n, n, ZZ.(magconvert(Vector, v)))
end

function TestingSFC.oscar_gf_to_magma_gf(F)
  p = Int(characteristic(F))
  return magf.GF(p)
end

function TestingSFC.magma_matrix_to_matrix_group(S, m)
  return mag"$(S)!$(m)"
end

function TestingSFC.magma_abelian_group(A::FinGenAbGroup)
  S, StoA = snf(A)
  e = BigInt.(S.snf)
  MA = mag"AbelianGroup($e)"

  AtoMA = function(x::FinGenAbGroupElem)
    @assert parent(x) === A
    co = BigInt.(Hecke._eltseq(preimage(StoA, x).coeff))
    return mag"$(MA)!$(co)"
  end

  MAtoA = function(y)
    a = StoA(S(magconvert(Vector{BigInt}, mag"Eltseq($(y))")))
    @assert parent(a) === A
    return a
  end

  for i in 1:10
    x = rand(A, 10)
    y = rand(A, 10)
    @assert MAtoA(AtoMA(x)) == x
    @assert AtoMA(x + y) == AtoMA(x) + AtoMA(y)
  end

  return MA, AtoMA, MAtoA
end

function TestingSFC.magma_hom(G, H, ims)
  return mag"hom<$(G) -> $(H) | $ims>"
end

function TestingSFC.magma_kernel(h)
  return mag"Kernel($h)"
  #return mag"Domain($mS)", mS
end

function TestingSFC.magma_sub(G, gs)
  mS = mag"S, mS := sub< $G | $(gs)>; return mS"
  return mag"Domain($(mS))", mS
end

function TestingSFC.ngens(G::MagmaObject)
  return magconvert(Int, mag"Ngens($G)")
end

function TestingSFC.order(G::MagmaObject)
  return ZZ(magconvert(BigInt, mag"#$(G)"));
end

function TestingSFC.magma_abelian_quotient(G::MagmaObject)
  mS = mag"n := #$(G); n; S, mS := AbelianQuotient($G); return mS"
  return mag"Codomain($(mS))", mS
end

function TestingSFC.magma_abelian_quotient_slow_of_matrix_group(v)
  p = Int.(characteristic(base_ring(v[1])))
  F = magf.GF(p)
  G = magf.GL(nrows(v[1]), F)
  @info "Translating matrices to Magma"
  #vv = [TestingSFC.oscar_matrix_to_magma_matrix(F, m) for m in v]
  vv = magseq()
  for m in v
    magp1.Append(vv, TestingSFC.oscar_matrix_to_magma_matrix(F, m))
  end
  @info "Creating group"
  mS = mag"S, mS := sub<$G | $vv>; n := #S; return mS";
  @info "done"
  S = mag"Domain($mS)"
  G = S
  g = mag"D := DerivedSubgroup($G); Q, GtoQ := quo< $G | D>; A, f := AbelianGroup(Q); g := GtoQ * f; return g"
  A = MagmaGroups.MagmaFinGenAbGroup(mag"Codomain($g)")
  Arel = mag"RelationMatrix($(MagmaGroups.data(A)))"
  dia = magconvert(Vector, mag"Diagonal($(Arel))")
  B = abelian_group(dia)
  BtoA = function(x::FinGenAbGroupElem)
    @assert parent(x) === B
    co = BigInt.(Hecke._eltseq(x.coeff))
    return MagmaGroups.MagmaGroupElem(A, mag"($(MagmaGroups.data(A)))!$(co)")
  end

  AtoB = function(y)
    a = B(magconvert(Vector{BigInt}, mag"Eltseq($(MagmaGroups.data(y)))"))
    @assert parent(a) === B
    return a
  end

  matrixtoab = function(M)
    mm = TestingSFC.oscar_matrix_to_magma_matrix(F, M)
    return AtoB(MagmaGroups.MagmaGroupElem(A, mag"$g($(S)!$(mm))"))
  end

  abtomatrix = function(y)
    yy = BtoA(y)
    m = mag"$(MagmaGroups.data(yy)) @@ $g"
    return TestingSFC.magma_matrix_to_oscar_matrix(base_ring(v[1]), m)
  end

  return B, matrixtoab, abtomatrix
end

function TestingSFC.magma_quotient(G::MagmaObject, H::MagmaObject)
  @info "Computing quotient"
  mS = mag"S, mS := quo<$G | $H>; return mS"
  return mag"Codomain($(mS))", mS
end

function TestingSFC.magma_derived_subgroup(G)
  return mag"DerivedSubgroup($G)"
end

function TestingSFC.gen(G::MagmaObject, i::Int)
  return mag"$(G).$(i)"
end

function TestingSFC.image(f::MagmaObject, x::MagmaObject)
  return mag"$x@$f"
end

function TestingSFC.preimage(f::MagmaObject, x::MagmaObject)
  return mag"$x@@$f"
end

function get_magma_abelian_groups(abelian_groups)
  v = Vector{Vector{Vector{Int}}}()
  for A in abelian_groups
    rA = rels(A)
    push!(v, [Int[rA[i, j] for j in 1:ncols(rA)] for i in 1:nrows(rA)])
  end
  return MagmaCall.magf.ConstructAbelianGroups(v)
end

function get_magma_automorphism_groups(mabelian_group)
  MagmaCall.magf.ConstructAutomorphismGroups(mabelian_group)
end

function magma_aut_setup(abelian_groups)
  mab = get_magma_abelian_groups(abelian_groups)
  maut = get_magma_automorphism_groups(mab)
  return mab, maut
end

function get_magma_permutation(abelian_groups, to_abelian_groups, to_quotient, mabelian, maut, x::Hecke.AbsOrdQuoRingElem)
  homs = get_automorphism_from_right_multiplication(x, abelian_groups, to_abelian_groups, to_quotient)
  imgs = Vector{Vector{Vector{Int}}}()
  for i in 1:length(homs)
    rA = matrix(homs[i])
    push!(imgs, [Int[rA[i, j] for j in 1:ncols(rA)] for i in 1:nrows(rA)])
  end

  p = MagmaCall.magf.ConstructElementInPermutationGroup(mabelian, maut, imgs)
end

mutable struct MagmaSetup
  Q
  abeliangroups
  to_abelian_groups
  to_quotient
  Mabeliangroups
  Mautomorphisms
end

function TestingSFC.magma_setup(Q::Hecke.AbsOrdQuoRing)
  abs, f, g = TestingSFC.embed_quotient_into_product_of_abelian_groups(TestingSFC.OscarGroup, Q)
  mab, maut = magma_aut_setup(abs)
  return MagmaSetup(Q, abs, f, g, mab, maut)
end

function magma_setup_abelianization(M::MagmaSetup)
  @assert length(M.abeliangroups) == 1
  magf.AbelianQuotient(Mautomorphisms[1])
end

Base.show(io::IO, M::MagmaSetup) = print(io, "Magma setup")

function transport_unit(M::MagmaSetup, a::Hecke.AbsOrdQuoRingElem)
  return get_magma_permutation(M.abeliangroups, M.to_abelian_groups, M.to_quotient, M.Mabeliangroups, M.Mautomorphisms, a)
end

function TestingSFC.__dispatch_nonsense_for_magma(::Type{TestingSFC.MagmaGroup}, Q) 
  return TestingSFC.__unit_group_abelianization_nonrecursive_permutation_group(TestingSFC.MagmaGroup, Q) 
end

end
