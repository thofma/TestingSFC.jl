function Hecke._is_principal(::Type{Hecke._PIPEichler}, I, O; side = :right, local_freeness::Bool = false)
  @assert side === :right
  @assert is_eichler(algebra(O))
  @vprintln :PIP 1 "is_principal (Eichler): dimension $(degree(O))"
  Id = denominator(I, O) * I
  if !local_freeness
    # local freeness not known
    for (p, ) in factor(discriminant(O))
      @vprintln :PIP 1 "is_principal (Eichler): Testing local freeness at $p"
      if !is_locally_free(O, Id, p, side = :right)[1]::Bool
        return false, zero(algebra(O))
      end
    end
  end
  # Now compute a conductor and make it coprime to the conductor
  if has_attribute(O, :pip_data)
    @vprintln :PIP 1 "is_principal (Eichler): pip data cached"
  end
  mC, M, toRmax, toR, RtoRquo, f = get_attribute!(O, :pip_data) do
    @vprintln :PIP 1 "is_principal (Eichler): pip data not cached"
    M = maximal_order(O)
    f = Hecke._get_a_twosided_conductor(O, M)
    fl, f = is_locally_radical_with_adjustment(M, f)
    f = f * O
    A = algebra(O)
    C, mC = center(A)
    g = Hecke._as_ideal_of_smaller_algebra(mC, f)
    ramified_places = Hecke.ramified_infinite_places_of_center(A)
    OC = maximal_order(C)
    @assert g * OC == g
    R, toR = ray_class_group(g*OC, ramified_places)
    Rmax, toRmax = ray_class_group(1*OC, ramified_places)
    @vprintln :PIP 1 "locally free class group maximal order: $(elementary_divisors(Rmax))"
    Q, OtoQ = quo(O, f)
    U = unit_group_generators(Q)
    img = FinGenAbGroupElem[ toR\(Hecke.normred_over_center(elem_in_algebra(OtoQ\u), mC)*OC) for u in U]
    Rquo, RtoRquo = quo(R, img)
    @vprintln :PIP 1 "locally free class group order: $(elementary_divisors(Rquo))"
    return mC, M, toRmax, toR, RtoRquo, f
  end
  if !isone(f + I)
    @vprintln :PIP 1 "is_principal (Eichler): Making coprime to conductor"
    II, sca = Hecke._coprime_integral_ideal_class(I, f)
    #_alpha2 = M(sca * _alpha)
    #@assert _alpha2 * M == II * M
  else
    #_alpha2 = M(_alpha)
    II = I
  end
  I = II
  @vprintln :PIP 1 "is_principal (Eichler): Extending ideal to maximal order"
  IM = I*M
  @vprintln :PIP 1 "is_principal (Eichler): Computing reduced norm"
  IMnorm = Hecke.normred_over_center(IM, mC)
  @vprintln :PIP 1 "is_principal (Eichler): Compute class of extended ideal"
  classofIM = toRmax\IMnorm
  if !is_zero(classofIM)
    @vprintln :PIP 1 "is_principal (Eichler): not stably free"
    return false
  end
  @vprintln :PIP 1 "is_principal (Eichler): stably free over maximal order (and thus free)"

  # Thus stably free over maximal order
  # Eichler => free over maximal order
  # normred(IM) = normred(beta)*OC if IM = beta*M
  @vprintln :PIP 1 "is_principal (Eichler): final test"
  @vprintln :PIP 1 "locally free class group order: $(elementary_divisors(codomain(RtoRquo)))"
  return is_zero(RtoRquo(toR\IMnorm))
end
