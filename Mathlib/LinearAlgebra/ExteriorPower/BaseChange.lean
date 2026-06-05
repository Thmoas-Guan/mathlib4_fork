/-
Copyright (c) 2026 Jingting Wang, Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jingting Wang, Nailin Guan
-/
module

public import Mathlib.LinearAlgebra.ExteriorPower.Basic

/-!

# Base change of exterior power

-/

public section

variable (R : Type*) [CommRing R] (M : Type*) [AddCommGroup M] [Module R M]

variable (S : Type*) [CommRing S] [Algebra R S]

open TensorProduct

variable (i : ℕ)

def exteriorPower.baseChangeIso (i : ℕ) : S ⊗[R] (⋀[R]^i M) ≃ₗ[S] ⋀[S]^i (S ⊗[R] M) := sorry

lemma exteriorPower.baseChangeIso_apply_tmul (i : ℕ) (m : Fin i → M) :
    exteriorPower.baseChangeIso R M S i (1 ⊗ₜ[R] (exteriorPower.ιMulti R i m)) =
    exteriorPower.ιMulti S i ((TensorProduct.mk R S M 1) ∘ m) := by
  sorry
