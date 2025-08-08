# This julia program is used in the proof of Theorem 13.4 of "Determination of the stably free cancellation property for orders"
# by Werner Bley, Tommy Hofmann and Henri Johnston. It searches the small groups database for finite groups G for which it is not 
# known whether the integral group ring Z[G] has SFC or not.
# 
# The parameters min_group_size and max_group_size set the range of orders of groups to search. Of course, this is limited by 
# the small groups database. Currently, this contains all finite groups of size up to 2000, excluding those of order 1024.
#
# IMPORTANT: groups of order 512, 1024, 1152, 1536, or 1920 will automatically be skipped because groups of order 1024 are not included 
# in the small groups database and because the small_group_identification function does not currently work for groups of order 512, 1152, 
# 1536, or 1920. These orders are picked out by the function has_small_group_identification.
#
# Note that Theorem 13.4 only considers groups of size at most 1023. See separate julia program that searches groups of order 512. */

export find_interesting_groups

function compute_without_sfc(min_group_size, max_group_size)
  # The follwing are finite groups G such that Z[G] fails SFC by Theorem 9.4. */
  without_sfc =
  [
  (16,12), (24,7), (32,14), (32,41), (36,7), (40,7), (64,14), (96,188), (96,198), (100,7), (480,960)
  ]

  # Append generalized quaternion groups G (also known as dicyclic groups) because then Z[G] fails SFC by Corollary 4.3 due to Swan.

  for i in 6:floor(Int, max_group_size//4)
    # Skip generalized quaternion groups of order 512, 1024, 1152, 1536 or 1920.
    if has_small_group_identification(4*i)
      push!(without_sfc, small_group_identification(quaternion_group(4*i)))
    end
  end
  return without_sfc
end

function compute_with_sfc(min_group_size, max_group_size)
  # The following are the groups G listed in Theorem 13.1 and are such that Z[G] does have SFC. 

  with_sfc =
  [
  (48,32), (96,66), (192,183), (192,1022), (240,94), (288,409), (384,580), (480,266), (480,962)
  ]

  # The following group G also has SFC by Theorem 4.7 due to Swan.

  push!(with_sfc, (576,5128))

  # By Theorem 4.8 due to Swan, we can append the direct products of groups in with_sfc with cyclic groups of odd order. 

  for gid in with_sfc
    for i in 3:2:19
      if gid[1]*i <= max_group_size && has_small_group_identification(gid[1]*i) && is_solvable(small_group(gid[1], gid[2]))
        push!(with_sfc, small_group_identification(direct_product(small_group(gid[1],gid[2]), cyclic_group(i))))
      end
    end
  end  

  # As above, but now append direct products with C3 x C3 = SmallGroup(9,2).

  for gid in with_sfc
    if (gid[1])*9 <= max_group_size && has_small_group_identification(gid[1]*9) && is_solvable(small_group(gid[1],gid[2]))
      with_sfc =  push!(with_sfc, small_group_identification(direct_product(small_group(gid[1],gid[2]),small_group(9, 2))))
    end
  end

  # Since SmallGroup(240,94) is not soluble, need to do the above steps for this separately. 

  for i in [3, 5, 7]
    push!(with_sfc, small_group_identification(direct_product(small_group(240, 94), cyclic_group(i))))
  end

  return with_sfc
end

# This only finds interesting groups of order n.
function find_interesting_groups_with_order(n, with_sfc, without_sfc)
  # The following are the binary polyhedral groups G such that Z[G] has SFC and m_H(G)=2. 

  bp_with_sfc_2_qcomp =
  [
  (16,9), (20,1), (48,28), (120,5)
  ]


  result = Tuple{Int, Int}[]
  # Skip groups of order 512, 1024, 1152, 1536, or 1920 for reasons explained above.
  if has_small_group_identification(n)
    for j in 1:number_of_small_groups(n)
      G = small_group(n, j)
      T = character_table(G)	
      # In the following, quat_count will be equal to m_H(G).
      quat_count = 0
      for chi in T
        if degree(chi) == 2 && indicator(chi) == -1
          quat_count += 1
        end
      end
      # If quat_count le 1 then Z[G] has SFC by Theorem 4.13 due to Nicholson. */
      # Thus it remains to consider the case quat_count ge 2. */
      if quat_count >= 2
        # Ignore groups G either in without_sfc or with_sfc. 
        if !((n, j) in without_sfc) && !((n, j) in with_sfc)
          has_fail_quotient = false
          has_sfc = false
          S = normal_subgroups(G)
          for l in 1:length(S)
            Q, = quo(G, S[l])
            quotientID = small_group_identification(Q)
            # The following checks whether Z[G] fails SFC by Corollary 9.8. 
            if quotientID in without_sfc
              has_fail_quotient = true
            end
            # The following checks whether Z[G] has SFC by Theorem 4.12 due to Nicholson. 
            if (quotientID in bp_with_sfc_2_qcomp) && (quat_count == 2)
              has_sfc = true
            end
            # The following checks whether Z[G] has SFC by Corollary 6.9. 
            if (quotientID == (48,32)) && (quat_count == 2)
              has_sfc = true
            end
          end
          # The following is an obvious check.
          if has_fail_quotient && has_sfc 
            error("Contradiction!")
          end
          # The following outputs groups G for which the above checks have not determined whether 
          # Z[G] has SFC or not.
          if !has_fail_quotient && !has_sfc
            println(n, " ", j)
            push!(result, (n, j))
          end
        end
      end
    end
  end
  return result
end

function find_interesting_groups(min_group_size = 1, max_group_size = 1023)

  without_sfc = compute_without_sfc(min_group_size, max_group_size)

  with_sfc = compute_with_sfc(min_group_size, max_group_size)

  # Now loop through groups in the small groups database.

  result = Tuple{Int, Int}[]

  for n in min_group_size:max_group_size
    append!(result, find_interesting_groups_with_order(n, with_sfc, without_sfc))
  end
  return result
end
