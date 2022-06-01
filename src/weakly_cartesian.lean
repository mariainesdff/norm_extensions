import analysis.normed_space.finite_dimension

variables (K V : Type*) [nondiscrete_normed_field K] [normed_group V] [normed_space K V]

-- Def 2.3.2/2
def is_weakly_cartesian : Prop :=
  ∀ (U : subspace K V) (hU : finite_dimensional K U), is_closed (U : set V)

--Prop. 2.3.3/4
lemma is_weakly_cartesian_over_complete_of_fd [complete_space K] (h : finite_dimensional K V) : 
  is_weakly_cartesian K V := 
begin
  unfreezingI{
  induction hn : finite_dimensional.finrank K V using nat.strong_rec' with n IH hn generalizing V,
  { intros U hU,
    by_cases hU_dim : finite_dimensional.finrank K U < n,
    { specialize IH (finite_dimensional.finrank K U) hU_dim U hU rfl,
      haveI hV_compl : complete_space V := finite_dimensional.complete K V,
      exact is_complete.is_closed (submodule.complete_of_finite_dimensional U), },
    { have hdim : finite_dimensional.finrank K ↥U = finite_dimensional.finrank K V,
      { rw ← hn at hU_dim,
        exact eq_of_le_of_not_lt U.finrank_le hU_dim },
      rw finite_dimensional.eq_top_of_finrank_eq hdim,
      exact submodule.closed_of_finite_dimensional _, }}}
end

lemma is_weakly_cartesian_over_complete [complete_space K] : 
  is_weakly_cartesian K V := sorry

instance is_complete_of_fd_over_complete [complete_space K] (h : finite_dimensional K V): 
  complete_space V := sorry