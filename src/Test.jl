function _find_all_possible_quotient_algebras_components(A::Hecke.AbstractAssociativeAlgebra, dimension_bound::Int; use_all_noneichler = true)
  dec = first.(decompose(A))
  deccentral = map(B -> Hecke._as_algebra_over_center(B)[1], dec)
  noneichler = findall(!is_eichler, deccentral)
  # Always take all non-eichler components
  if use_all_noneichler
    dimension_bound_rest = dimension_bound - sum(dim(dec[i]) for i in noneichler)
  else
    dimension_bound_rest = dimension_bound
  end
  eichler = setdiff(collect(1:length(dec)), noneichler)
  @info "Eichler indicies: $(eichler)"
  @info "Non-Eichler indicies: $(noneichler)"
  @info "Eichler dims: $([dim(dec[i]) for i in eichler])"
  @info "Non-Eichler dims: $([dim(dec[i]) for i in noneichler])"

  good_indices = Int[]
  index_translate = Dict{Int, Int}()
  k = 0
  for i in eichler
    if dim(dec[i]) > dimension_bound_rest
      continue
    end
    k += 1
    push!(good_indices, i)
    index_translate[k] = i
  end
  rres = Vector{Int}[]
  if use_all_noneichler
    res = _find_all_knapsack_leq([dim(dec[i]) for i in good_indices], dimension_bound_rest)
    l = nrows(res)
    @assert k == ncols(res)
    rres = [append!([index_translate[j] for j in 1:k if res[i, j] > 0], noneichler) for i in 1:l]
    filter!(l -> length(intersect(l, noneichler)) != length(l), rres)
  else
    for i in noneichler
      if dim(dec[i]) > dimension_bound_rest
        continue
      end
      k += 1
      push!(good_indices, i)
      index_translate[k] = i
    end
    # 
    res = _find_all_knapsack_leq([dim(dec[i]) for i in good_indices], dimension_bound)
    l = nrows(res)
    rres = Vector{Int}[]
    for i in 1:l
      ll = [index_translate[j] for j in 1:k if res[i, j] > 0]
      #if length(intersect(ll, noneichler)) <= 1 || length(intersect(ll, noneichler)) == length(ll)
      #  continue
      #end
      push!(rres, ll)
    end
  end
  @info "Number of candidate quotients: $(length(rres))"
  sort!(rres, by = ll -> sum(dim(dec[i]) for i in ll; init = 0))
  return rres
end

function _find_all_knapsack_leq(w::Vector{Int}, B::Int)
  n = length(w)
  I = identity_matrix(ZZ, n)
  II = -identity_matrix(ZZ, n)
  A = [matrix(ZZ, 1, n, w); I; II]
  b = matrix(ZZ, 2*n + 1, 1, append!([B], fill(1, (n, )), fill(0, (n, ))))
  return Oscar.solve_ineq(A, b)
end

function _try_proving_non_sfc_using_quotients(Gamma, dimension_bound::Int = 48; use_all_noneichler::Bool = false, minimal::Bool = false)
  return _try_proving_non_sfc_using_quotients(OscarGroup, Gamma, dimension_bound; use_all_noneichler, minimal)
end

function _try_proving_non_sfc_using_quotients(::Type{T}, Gamma, dimension_bound::Int = 48; use_all_noneichler::Bool = false, minimal::Bool = false) where {T}
  cand = _find_all_possible_quotient_algebras_components(algebra(Gamma), dimension_bound; use_all_noneichler)
  # all candidates cand contain the non-eichler components,
  # so min(#cand) = is the number of non-eichler components
  for c in cand
    @info "Doing $c"
    if length(c) == 0
      continue
    end
    _, p = Hecke.product_of_components_with_projection(algebra(Gamma), c)
    GammaGamma = p(Gamma)
    if is_maximal(GammaGamma)
      @info "Quotient is maximal ... skipping"
      continue
    end
    if is_eichler(algebra(GammaGamma))
      @info "Quotient is Eichler ... skipping"
      continue
    end
    @info "Degree of quotient: $(degree(GammaGamma))"
    fl = has_not_stably_free_cancellation_probably(GammaGamma, 100; s1_method = :heuristic)
    @info "has_not_stably_free_cancellation_probably: $fl"
    if fl
      return true, GammaGamma
    else
      if minimal
        @info "Found a quotient, which has probably SFC, but lets prove it because we look for a minimal quotient"
        if _is_purely_noneichler(GammaGamma)
          @assert has_stably_free_cancellation_brute_force(T, GammaGamma)
        else
          @assert proof_via_standard_eichler_splitting(T, GammaGamma)
        end
      end
    end
  end
  return false, Gamma
end

function _try_proving_not_free_using_quotients(I, Gamma, dimension_bound::Int = 48; use_all_noneichler::Bool = false, minimal::Bool = false)
  cand = _find_all_possible_quotient_algebras_components(algebra(Gamma), dimension_bound; use_all_noneichler)
  # all candidates cand contain the non-eichler components,
  # so min(#cand) = is the number of non-eichler components
  for c in cand
    @info "Doing $c"
    if length(c) == 0
      continue
    end
    if length(c) == 1
      continue
    end
    _, p = Hecke.product_of_components_with_projection(algebra(Gamma), c)
    Hecke._transport_refined_wedderburn_decomposition_forward(p)
    GammaGamma = p(Gamma)
    C, mC = locally_free_class_group_with_disc_log(GammaGamma; check = false)
    II = p(I)
    local fl
    try
      fl = is_zero(mC(II * GammaGamma))
    catch e
      @error e
      continue
    end

    #if is_maximal(GammaGamma)
    #  @info "Quotient is maximal ... skipping"
    #  continue
    #end
    #@info "Degree of quotient: $(degree(GammaGamma))"
    #@assert II * GammaGamma == II
    #@show is_eichler(algebra(GammaGamma))
    #fl = Hecke._is_principal(II * GammaGamma, GammaGamma)
    #@info "free: $fl"
    if !fl
      return true, GammaGamma
    end
  end
  return false, Gamma
end
