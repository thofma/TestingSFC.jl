intrinsic ConstructAbelianGroups(rel_matrices::Any) -> Any
	{}
	nab := #rel_matrices;
	Abs := [* *];
	for i in [1..nab] do
		M := rel_matrices[i];
		F := FreeAbelianGroup(#(M[1]));
		Q := [F!r : r in M];
		A, m := quo<F | Q>;
		Append(~Abs, <A, m>);
	end for;
	return Abs;
end intrinsic;

intrinsic ConstructAutomorphismGroups(abelian_groups::Any) -> Any
	{}
	nab := #abelian_groups;
	auts := [AutomorphismGroup(A[1]) : A in abelian_groups];
	auts_perms_maps := [PermutationRepresentation(Aut) : Aut in auts];
	auts_perms := [Codomain(m) : m in auts_perms_maps];
	"Degrees:", [Degree(A) : A in auts_perms];
	// auts_perms is AutToP, P
	D, injs, projs := DirectProduct(auts_perms);
	return <D, injs, projs, auts_perms_maps>;
end intrinsic;

intrinsic ConstructListOfAutomorphisms(abelian_groups::Any, imgs::Any) -> Any
	{}
	nab := #abelian_groups;
	assert #imgs eq nab;
	homs := [* *];
	for i in [1..nab] do
		A, m := Explode(abelian_groups[i]);
		F := Domain(m);
		assert Ngens(F) eq #imgs[i]; 
		homF := hom<F -> F | [F!r : r in imgs[i]]>;
		homA := hom<A -> A | [m(homF(A.i@@m)) : i in [1..Ngens(A)]]>;
		Append(~homs, homA);
	end for;
	return homs;
end intrinsic;

intrinsic ConstructElementInPermutationGroup(abelian_groups::Any, aut_data::Any, imgs::Any) -> Any
	{}
	D, injs, projcs, auts_perms_maps := Explode(aut_data);
	nab := #abelian_groups;
	homs := ConstructListOfAutomorphisms(abelian_groups, imgs);
	e := Identity(D);
	for i in [1..nab] do
		A := Domain(auts_perms_maps[i]);
		pi := auts_perms_maps[i](A!(homs[i]));
		e := e * injs[i](pi);
	end for;
	return e;
end intrinsic;

intrinsic write_array(x::Any, File) -> Any
	{}
  return true;
end intrinsic;

intrinsic write_arrays(x::Any, File) -> Any
  {}
  k := #x;
  SetColumns(0);
  for i in [1..k] do
    Write(File, x[i]);
  end for;
  return true;
end intrinsic;
