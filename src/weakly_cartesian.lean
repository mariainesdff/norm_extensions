import analysis.normed_space.basic

variables {K V : Type*} [normed_field K] [semi_normed_group V] [normed_space K V]

def is_weakly_cartesian : Prop :=
  ∀ (U : subspace K V) (hU : finite_dimensional K U), is_closed (U : set V)




