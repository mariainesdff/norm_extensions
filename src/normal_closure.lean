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

--universe u

section field_range

def alg_hom.field_range {F K L : Type*} [field F] [field K] [field L] [algebra F K]
  [algebra F L] (φ : K →ₐ[F] L) : intermediate_field F L :=
{ ..φ.range,
  ..φ.to_ring_hom.field_range }

/-- Restrict the codomain of a alg_hom `f` to `f.range`.

This is the bundled version of `set.range_factorization`. -/
@[reducible] def alg_hom.field_range_restrict {F K L : Type*} [field F] [field K] [field L] [algebra F K]
  [algebra F L] (φ : K →ₐ[F] L) : K →ₐ[F] φ.field_range :=
φ.cod_restrict φ.range φ.mem_range_self

end field_range

/- section inclusion

noncomputable lemma intermediate_field.inclusion {K L : Type*} [field K] [field L] [algebra K L]
  {S T : intermediate_field K L} (h : S ≤ T) : (↥S →ₐ[K] ↥T) :=
{ to_fun := set.inclusion h,
  map_one' := rfl,
  map_add' := λ _ _, rfl,
  map_mul' := λ _ _, rfl,
  map_zero' := rfl,
  commutes' := λ _, rfl }

end inclusion -/

variables (K L : Type*) [field K] [field L] [algebra K L]

noncomputable! def normal_closure : intermediate_field K (algebraic_closure L) :=
supr (λ φ : (L →ₐ[K] algebraic_closure L), φ.field_range)

namespace normal_closure

lemma le_closure : (is_scalar_tower.to_alg_hom K L (algebraic_closure L)).field_range ≤
  normal_closure K L :=
le_supr _ _

noncomputable instance : algebra L (normal_closure K L) := ring_hom.to_algebra
((intermediate_field.inclusion (le_closure K L)).comp
  ((is_scalar_tower.to_alg_hom K L (algebraic_closure L)).field_range_restrict))

lemma is_normal (h : algebra.is_algebraic K L) : normal K (normal_closure K L) := sorry

lemma is_algebraic (h : algebra.is_algebraic K L) : algebra.is_algebraic K (normal_closure K L) :=
sorry

instance : is_scalar_tower K L (normal_closure K L) := sorry

lemma is_finite_dimensional [finite_dimensional K L] : finite_dimensional K (normal_closure K L) :=
sorry

end normal_closure