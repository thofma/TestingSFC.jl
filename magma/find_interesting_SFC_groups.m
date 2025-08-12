/* This magma program is used in the proof of Theorem 13.4 of "Determination of the stably free cancellation property for orders"
by Werner Bley, Tommy Hofmann and Henri Johnston. It searches the small groups database for finite groups G for which it is not 
known whether the integral group ring Z[G] has SFC or not. */

/* The following two parameters set the range of orders of groups to search. Of course, this is limited by the small groups database.
Currently, this contains all finite groups of size up to 2000, excluding those of order 1024.*/  

min_group_size := 1;
max_group_size := 1023;  /* Currently should be at most 2000. */

/* IMPORTANT: groups of order 512, 1024, 1152, 1536, or 1920 will automatically be skipped because groups of order 1024 are not included 
in the small groups database and because the IdentifyGroup function does not currently work for groups of order 512, 1152, 1536, or 1920. 
These orders are picked out by the function CanIdentifyGroup.
*/

/* Note that Theorem 13.4 only considers groups of size at most 1023. See separate magma program that searches groups of order 512. */

/* The follwing are finite groups G such that Z[G] fails SFC by Theorem 9.4. */

without_sfc :=
[
<16,12>, <24,7>, <32,14>, <32,41>, <36,7>, <40,7>, <64,14>, <96,188>, <96,198>, <100,7>, <480,960>
];

/* Append generalized quaternion groups G (also known as dicyclic groups) because then Z[G] fails SFC by Corollary 4.3 due to Swan. */  

for i in [6..Floor(max_group_size/4)] do
	/* Skip generalized quaternion groups of order 512, 1024, 1152, 1536 or 1920. */
	if CanIdentifyGroup(4*i) then 
 		 without_sfc := Append(without_sfc,IdentifyGroup(PCGroup(DicyclicGroup(i))));
	end if;
end for;

/* The following are the binary polyhedral groups G such that Z[G] has SFC and m_H(G)=2. */

bp_with_sfc_2_qcomp :=
[
<16,9>, <20,1>, <48,28>, <120,5>
];

/* The following are the groups G listed in Theorem 13.1 and are such that Z[G] does have SFC. */

with_sfc :=
[
<48,32>, <96,66>, <192,183>, <192,1022>, <240,94>, <288,409>, <384,580>, <480,266>, <480,962>
]; 

/* The following group G also has SFC by Theorem 4.7 due to Swan. */

with_sfc := Append(with_sfc, <576,5128>);

/* By Theorem 4.8 due to Swan, we can append the direct products of groups in with_sfc with cyclic groups of odd order. */

for gid in with_sfc do
	for i := 3 to 19 by 2 do
		if gid[1]*i le max_group_size and CanIdentifyGroup(gid[1]*i) and IsSolvable(SmallGroup(gid[1],gid[2])) then
			with_sfc :=  Append(with_sfc,IdentifyGroup(DirectProduct(SmallGroup(gid[1],gid[2]),SmallGroup(i,1))));
		end if;
	end for;
end for;  

/* As above, but now append direct products with C3 x C3 = SmallGroup(9,2). */

for gid in with_sfc do
	if (gid[1])*9 le max_group_size and CanIdentifyGroup(gid[1]*9) and IsSolvable(SmallGroup(gid[1],gid[2])) then
		 with_sfc :=  Append(with_sfc,IdentifyGroup(DirectProduct(SmallGroup(gid[1],gid[2]),SmallGroup(9,2))));
        end if;
end for;

/* Since SmallGroup(240,94) is not soluble, need to do the above steps for this separately. */

with_sfc := Append(with_sfc,IdentifyGroup(DirectProduct(SmallGroup(240,94),PermutationGroup< 3 | (1,2,3) >)));
with_sfc := Append(with_sfc,IdentifyGroup(DirectProduct(SmallGroup(240,94),PermutationGroup< 5 | (1,2,3,4,5) >)));
with_sfc := Append(with_sfc,IdentifyGroup(DirectProduct(SmallGroup(240,94),PermutationGroup< 7 | (1,2,3,4,5,6,7) >)));

/* Now loop through groups in the small groups database. */

for n in [min_group_size..max_group_size] do
	/* Skip groups of order 512, 1024, 1152, 1536, or 1920 for reasons explained above. */
	if CanIdentifyGroup(n) then 	
		for j in [1..NumberOfSmallGroups(n)] do
			G := SmallGroup(n,j);
			T := CharacterTable(G);	
			/* In the following, quat_count will be equal to m_H(G). */
			quat_count := 0;
			for k in [1..#T] do
				if (Indicator(T[k]) eq -1) and (Degree(T[k]) eq 2)  then
					 quat_count := quat_count + 1;
				end if; 
			end for;
			/* If quat_count le 1 then Z[G] has SFC by Theorem 4.13 due to Nicholson. */
			/* Thus it remains to consider the case quat_count ge 2. */
			if (quat_count ge 2) then
				/* Ignore groups G either in without_sfc or with_sfc. */
				if not(<n,j> in without_sfc) and not(<n,j> in with_sfc) then
					has_fail_quotient := false;
					has_sfc := false;
					S := NormalSubgroups(G);
					for l in [1..#S] do
						Q := G/(S[l]`subgroup);
						quotientID := IdentifyGroup(Q);
						/* The following checks whether Z[G] fails SFC by Corollary 9.8. */
						if quotientID in without_sfc then
							has_fail_quotient := true;
						end if;
						/* The following checks whether Z[G] has SFC by Theorem 4.12 due to Nicholson. */
						if (quotientID in bp_with_sfc_2_qcomp) and (quat_count eq 2) then
							has_sfc  := true;	
						end if;
						/* The following checks whether Z[G] has SFC by Corollary 6.9. */
						if (quotientID eq <48,32>) and (quat_count eq 2) then
							has_sfc := true;			
						end if;
					end for;
					/* The following is an obvious check. */
					if has_fail_quotient and has_sfc then
						print "Contradiction!";
					end if;
					/* The following outputs groups G for which the above checks have not determined whether 
					Z[G] has SFC or not. */
          	if not(has_fail_quotient) and not(has_sfc) then
            	print n,j;
          	end if;
				end if;
			end if;
		end for;
	end if;
end for;
