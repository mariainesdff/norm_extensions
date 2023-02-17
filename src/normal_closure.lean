/-
Copyright (c) 2023 María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández
-/

import field_theory.normal
import field_theory.is_alg_closed.algebraic_closure

/-!
# Normal closures

## Main Results

- `normal_closure.is_algebraic` : If `L/K` is an algebraic field extension, then the normal closure
  of `L/K` in the algebraic closure of `L` is an algebraic extension of `K`.

## Tags

normal, normal_closure, algebraic, is_algebraic
-/


variables (K L : Type*) [field K] [field L] [algebra K L]

namespace normal_closure

/-- If `L/K` is an algebraic field extension, then the normal closure of `L/K` in the algebraic
closure of `L` is an algebraic extension of `K`. -/
lemma is_algebraic (h : algebra.is_algebraic K L) : 
  algebra.is_algebraic K (normal_closure K L (algebraic_closure L)) :=
algebra.is_algebraic_trans h 
  (λ x, intermediate_field.is_algebraic_iff.mpr (algebraic_closure.is_algebraic _ _))

end normal_closure