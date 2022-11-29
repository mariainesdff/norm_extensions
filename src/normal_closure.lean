/-
Copyright (c) 2022 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard
-/

import field_theory.normal
import field_theory.is_alg_closed.algebraic_closure

/-!
# Normal closures

Let L/K be a finite field extension. The normal closure N/L of L/K is a finite extension
N/L such that N/K is normal and which is informally "the smallest extension with this property".
More formally we could say that if M/L is algebraic and M/K is normal then there exists
a morphism of K-algebras `N →ₐ[K] M`. Note that this morphism may not be unique, and
indeed `N` is only defined up to a non-unique isomorphism in general.

## Main Definitions

- `normal_closure K L` where `L` is a field extension of the field `K`, of finite degree.
-/

variables (K L : Type*) [field K] [field L] [algebra K L]

namespace normal_closure

lemma is_algebraic (h : algebra.is_algebraic K L) : 
  algebra.is_algebraic K (normal_closure K L (algebraic_closure L)) :=
begin
  have hL : algebra.is_algebraic L ↥(normal_closure K L (algebraic_closure L)),
  { intro x,
    obtain ⟨p, hp0, hp_eval⟩ := algebraic_closure.is_algebraic L x,
    use [p, hp0],
    rw [subalgebra.aeval_coe] at hp_eval,
    norm_cast at hp_eval,
    exact hp_eval },
  exact algebra.is_algebraic_trans h hL,
end

end normal_closure