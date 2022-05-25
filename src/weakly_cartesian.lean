import analysis.normed_space.basic

variables (K V : Type*) [normed_field K] [semi_normed_group V] [normed_space K V]


-- Def 2.3.2/2
def is_weakly_cartesian : Prop :=
  ∀ (U : subspace K V) (hU : finite_dimensional K U), is_closed (U : set V)


--Prop. 2.3.3/4
lemma is_weakly_cartesian_over_complete_of_fd [complete_space K] (h : finite_dimensional K V) : 
  is_weakly_cartesian K V := sorry

lemma is_weakly_cartesian_over_complete [complete_space K] : 
  is_weakly_cartesian K V := sorry

instance is_complete_of_fd_over_complete [complete_space K] (h : finite_dimensional K V): 
  complete_space V := sorry