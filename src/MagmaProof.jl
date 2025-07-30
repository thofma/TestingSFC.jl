#function get_magma_abelian_groups(abelian_groups)
#  v = Vector{Vector{Vector{Int}}}()
#  for A in abelian_groups
#    rA = rels(A)
#    push!(v, [Int[rA[i, j] for j in 1:ncols(rA)] for i in 1:nrows(rA)])
#  end
#  return MagmaCall.magf.ConstructAbelianGroups(v)
#end
#
#function get_magma_automorphism_groups(mabelian_group)
#  MagmaCall.magf.ConstructAutomorphismGroups(mabelian_group)
#end
#
#function magma_aut_setup(abelian_groups)
#  mab = get_magma_abelian_groups(abelian_groups)
#  maut = get_magma_automorphism_groups(mab)
#  return mab, maut
#end
#
#function get_magma_permutation(abelian_groups, to_abelian_groups, to_quotient, mabelian, maut, x::Hecke.AbsOrdQuoRingElem)
#  homs = get_automorphism_from_right_multiplication(x, abelian_groups, to_abelian_groups, to_quotient)
#  imgs = Vector{Vector{Vector{Int}}}()
#  for i in 1:length(homs)
#    rA = matrix(homs[i])
#    push!(imgs, [Int[rA[i, j] for j in 1:ncols(rA)] for i in 1:nrows(rA)])
#  end
#
#  p = MagmaCall.magf.ConstructElementInPermutationGroup(mabelian, maut, imgs)
#end
#
#mutable struct MagmaSetup
#  Q
#  abeliangroups
#  to_abelian_groups
#  to_quotient
#  Mabeliangroups
#  Mautomorphisms
#end
#
## function TestingSFC.magma_setup(Q::Hecke.AbsOrdQuoRing)
##   abs, f, g = TestingSFC.embed_quotient_into_product_of_abelian_groups(Q)
##   mab, maut = magma_aut_setup(abs)
##   return MagmaSetup(Q, abs, f, g, mab, maut)
## end
#
#Base.show(io::IO, M::MagmaSetup) = print(io, "Magma setup")
#
#function transport_unit(M::MagmaSetup, a::Hecke.AbsOrdQuoRingElem)
#  return get_magma_permutation(M.abeliangroups, M.to_abelian_groups, M.to_quotient, M.Mabeliangroups, M.Mautomorphisms, a)
#end
#
#function has_stably_free_cancellation_magma(F)
#  O = F.R
#  M2 = F.M2
#  F2 = F.f2 * M2
#  Q, = quo(M2, F2)
#  M = MagmaSetup(Q)
#  ugens = Q.(Hecke.K1_order_mod_conductor(M2, M2, F2, do_units = true))
#  return ugens
#  _sigma2_gens = _sigma_generators(F, 2)
#  if isempty(_sigma2_gens)
#    _sigma2_gens = [one(F.R)]
#  end
#  @assert parent(_sigma2_gens[1]) == F.R
#  sigma2_gens = [Q(M2(F.p2(elem_in_algebra(b)))) for b in _sigma2_gens]
#  ugroupgens = [transport_unit(M, u) for u in ugens]
#  usgens = [transport_unit(M, u) for u in sigma2_gens]
#  T2 = Hecke._unit_group_generators_maximal(M2)
#  T2gensproj = [transport_unit(M, Q(M2(u))) for u in T2]
#  D = M.Mautomorphisms[1] # this is the big permutation group
#  @info MagmaCall.magf.Order(D)
#  S = MagmaCall.mag"sub<$D | $ugroupgens>"
#  @info MagmaCall.magf.Order(S)
#  SigmaSubgroup = MagmaCall.mag"sub<$S | $usgens>"
#  @info MagmaCall.magf.Order(SigmaSubgroup)
#  T2Subgroup = MagmaCall.mag"sub<$S | $T2gensproj>"
#  @info MagmaCall.magf.Order(T2Subgroup)
#  res1, res2 = MagmaCall.magf2.DoubleCosetRepresentatives(S, SigmaSubgroup, T2Subgroup)
#  n = magconvert(Int, MagmaCall.mag"#$res1")
#  @info "Number of double cosets: $n"
#  FF = MagmaCall.magf.FreeGroup(length(ugens))
#  f = MagmaCall.mag"hom<$FF -> $S | $ugroupgens>"
#  @info "Writing the Magma elements to file"
#  A = MagmaCall.mag"[ElementToSequence($res1[i]@@$f) : i in [1..$n]]";
#  @assert length(A) == n
#  words = read_vector_of_vector_from_magma(A)
#  @assert length(words) == n
#  Qfake = Hecke.FakeAbsOrdQuoRing(M2, F2)
#  ugensfast = [Qfake(u.elem) for u in ugens]
#  ugensfastinv = [Qfake(inv(u).elem) for u in ugens]
#  @info "Iterating over all double cosets"
#  for i in 1:n
#    print("\33[2K\r")
#    printstyled("$i/$n:"; color = :cyan, bold = true)
#    o = word_to_element(words[i], ugensfast, ugensfastinv, Qfake)
#    _beta = lift(o)
#    #@assert transport_unit(M, Q(_beta)) == res1[i]
#    __beta = F.e2 * haspreimage(F.p2, elem_in_algebra(_beta))[2]
#    beta = (F.M)(F.e1 + __beta)
#    #@assert F.M2(F.p2(elem_in_algebra(beta))) == _beta
#
#    printstyled(" testing stable freeness"; color = :cyan, bold = true)
#    fl = _defines_stably_free_generalized_swan_module(beta, O, F.f)
#
#    if !fl
#      printstyled(", not stably free"; color = :cyan, bold = true)
#      continue
#    else
#      printstyled(", stably free"; color = :cyan, bold = true)
#    end
#
#    printstyled(", testing freeness"; color = :cyan, bold = true)
#    fl = _s1_method(O, elem_in_algebra(beta), F)
#    if !fl
#      println()
#      return false
#    end
#  end
#  println()
#  return true
#end
#
#function read_vector_of_vector_from_magma(A)
#  mtmp = tempname()
#  @time MagmaCall.mag"write_arrays($A, $mtmp)"
#  @time res = _read_magma_file_fast(mtmp)
#  @assert length(res) == length(A)
#  rm(mtmp; force = true)
#  return res
#end
#
#function _read_magma_file(file)
#  res = Vector{Vector{Int}}()
#  for l in eachline(file)
#    x = TestingSFC.eval(Meta.parse(l))
#    push!(res, x)
#  end
#  return res
#end
#
#function _read_magma_file_fast(file)
#  # clean
#  run(`sed -ir 's/ //g' $file`)
#  res = Vector{Vector{Int}}()
#  open(file) do io
#    while !eof(io)
#      b, z = Hecke._parse(Vector{Int}, io)
#      push!(res, z)
#      if eof(io)
#        break
#      end
#    end
#  end
#  return res
#end
