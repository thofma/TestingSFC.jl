# This julia program is used in the proof of Theorem 13.4 of "Determination of the stably free cancellation property for orders"
# by Werner Bley, Tommy Hofmann and Henri Johnston. It searches the small groups database for finite groups G for which it is not 
# known whether the integral group ring Z[G] has SFC or not. The only group ID it should output is (512,2044), which is the generalised
# quaternion group order 512. We know that for G=(512,2044), the group ring Z[G] fails SFC by Corollary 4.3 due to Swan.

# This implementation is only for groups of order 512. See separate program for groups of other orders. Note that the other program
# is more informative because in this program we can skip many of the checks. 

export find_interesting_groups_512

function find_interesting_groups_512()

# The follwing are finite groups G of 2-power order such that Z[G] fails SFC by Theorem 9.4.
  
  without_sfc =
  [
  (16,12), (32,14), (32,41), (64,14)
  ]

  # Append generalized quaternion groups G (also known as dicyclic groups) of 2-power order 
  # and of order striclty less than 512 because then Z[G] fails SFC by Corollary 4.3 due to Swan. 

  for i in 3:6
    push!(without_sfc, small_group_identification(quaternion_group(4 * 2^i)))
  end

# The following are the binary polyhedral groups G of 2-power order such that Z[G] has SFC and m_H(G)=2.

  bp_with_sfc_2_qcomp =
  [
  (16,9)
  ]

  # Now loop through groups of order 512 in the small groups database.
  
  result = Tuple{Int, Int}[]

  for j in 1:number_of_small_groups(512)
    G = small_group(512, j)
    if is_abelian(G)
      continue
    end
    T = character_table(G)	
    # In the following, quat_count will be equal to m_H(G).
    quat_count = 0
    for chi in T
      if degree(Int, chi) == 2 && indicator(chi) == -1
         quat_count += 1
      end
    end
    # If quat_count le 1 then Z[G] has SFC by Theorem 4.13 due to Nicholson.
    # Thus it remains to consider the case quat_count >= 2.
    if quat_count >= 2
      has_fail_quotient = false
      has_sfc = false
      S = normal_subgroups(G)
      for l in 1:length(S)
        Q, = quo(G, S[l])
        # The following check ensures that we skip the trivial quotient. 
        if order(Q) != 512
          quotientID = small_group_identification(Q)
          # The following checks whether Z[G] fails SFC by Corollary 9.8.
          if quotientID in without_sfc
            has_fail_quotient = true
          end
          # The following checks whether Z[G] has SFC by Theorem 4.12 due to Nicholson.
          if (quotientID in bp_with_sfc_2_qcomp) && (quat_count == 2)
            has_sfc = true
          end
        end
      end
      # The following is an obvious check.
      if has_fail_quotient && has_sfc
        error("Contradiction!")
      end
      # The following outputs groups G for which the above checks have not determined whether 
      # Z[G] has SFC or not. 
      if !has_fail_quotient && !has_sfc
        println(512, " ", j)
        push!(result, (512, j))
      end
    end
  end
  return result
end
