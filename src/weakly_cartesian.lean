import analysis.normed_space.finite_dimension

variables (K V : Type*) [nontrivially_normed_field K] [normed_add_comm_group V] [normed_space K V]

-- Def 2.3.2/2
def is_weakly_cartesian : Prop :=
  ∀ (U : subspace K V) (hU : finite_dimensional K U), is_closed (U : set V)

--Prop. 2.3.3/4
lemma is_weakly_cartesian_over_complete_of_fd [complete_space K] (h : finite_dimensional K V) : 
  is_weakly_cartesian K V := 
λ U hU, submodule.closed_of_finite_dimensional _

lemma is_weakly_cartesian_over_complete [complete_space K] : 
  is_weakly_cartesian K V :=
by { introsI U hU, exact submodule.closed_of_finite_dimensional U }

instance is_complete_of_fd_over_complete [complete_space K] (h : finite_dimensional K V): 
  complete_space V := 
finite_dimensional.complete K V

-- TODO: probably won't need is_weakly_cartesian, since these lemmas are essentially in mathlib