/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.RingTheory.KoszulComplex.ExteriorAlgebraProduct

/-!

# Exterior power of product module

-/

public section

universe u

variable (R : Type u) [CommRing R]

variable (M N : Type*) [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

open TensorProduct

def ExteriorAlgebra.prodEquivProd :
    (ExteriorAlgebra R M × ExteriorAlgebra R M) ≃ₗ[R] ExteriorAlgebra R (M × R) := sorry

lemma ExteriorAlgebra.prodEquivProd_comp_inl :
    (ExteriorAlgebra.prodEquivProd R M).comp (LinearMap.inl R _ _) =
      ExteriorAlgebra.map (LinearMap.inl R M R) := by
  sorry

lemma ExteriorAlgebra.prodEquivProd_apply_snd (a : ExteriorAlgebra R M) :
    ExteriorAlgebra.prodEquivProd R M (0, a) =
      (ExteriorAlgebra.map (LinearMap.inl R M R) a) * ExteriorAlgebra.ι R ((0, 1) : M × R) := by
  sorry

lemma ExteriorAlgebra.prodEquivProd_mem_exteriorPower (i : ℕ) (x y : ExteriorAlgebra R M) :
    ExteriorAlgebra.prodEquivProd R M (x, y) ∈ ⋀[R]^(i + 1) (M × R) ↔
    (x ∈ ⋀[R]^(i + 1) M ∧ y ∈ ⋀[R]^i M) := by
  sorry

def exteriorPowerProdEquivProd (i : ℕ) : (⋀[R]^(i + 1) M × ⋀[R]^i M) ≃ₗ[R] ⋀[R]^(i + 1) (M × R) :=
  sorry

lemma exteriorPowerProdEquivProd_apply_inl_ιMulti (i : ℕ) (m : Fin (i + 1) → M) :
    (exteriorPowerProdEquivProd R M i) (exteriorPower.ιMulti R (i + 1) m, 0) =
      exteriorPower.ιMulti R (i + 1) ((LinearMap.inl R M R) ∘ m) := by
  sorry

lemma exteriorPowerProdEquivProd_comp_inl (i : ℕ) :
    (exteriorPowerProdEquivProd R M i).toLinearMap.comp (LinearMap.inl R _ _) =
    exteriorPower.map (i + 1) (LinearMap.inl R _ _) := by
  ext m
  have : Matrix.vecTail ((LinearMap.inl R M R) ∘ m) =
    fun j ↦ Matrix.vecTail (fun i ↦ Prod.mk (m i)) j 0 := rfl
  simp [exteriorPowerProdEquivProd_apply_inl_ιMulti, ← this]

lemma exteriorPowerProdEquivProd_apply_inr_ιMulti (i : ℕ) (m : Fin i → M) :
    (exteriorPowerProdEquivProd R M i) (0, exteriorPower.ιMulti R i m) =
      ExteriorAlgebra.ιMulti R i ((LinearMap.inl R M R) ∘ m) *
        ExteriorAlgebra.ι R ((0, 1) : M × R) := by
  sorry
