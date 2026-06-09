/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.LinearAlgebra.ExteriorAlgebra.Product

/-!

# Exterior power of product module

-/

public section

universe u

variable (R : Type u) [CommRing R]

variable (M N : Type*) [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

open TensorProduct

lemma exteriorPower_prod_eq_map_sup (i : ℕ) :
    ⋀[R]^(i + 1) (M × R) = Submodule.map (ExteriorAlgebra.prodEquivTensor R M R).symm.toLinearMap
      (((map (⋀[R]^(i + 1) M).subtype (⋀[R]^0 R).subtype).range ⊔ (map (⋀[R]^i M).subtype
        (⋀[R]^1 R).subtype).range).map (GradedTensorProduct.of R _ _).toLinearMap) := by
  --try write rightside to span of tmul of ιMulti
  --TensorProduct.range_map_eq_span_tmul
  sorry

def exteriorPowerProdEquivProd (i : ℕ) : ⋀[R]^(i + 1) (M × R) ≃ₗ[R] ⋀[R]^(i + 1) M × ⋀[R]^i M :=
  sorry

lemma exteriorPowerProdEquivProd_symm_comp_inl (i : ℕ) :
    (exteriorPowerProdEquivProd R M i).symm.toLinearMap.comp (LinearMap.inl R _ _) =
    exteriorPower.map (i + 1) (LinearMap.inl R _ _) := by
  ext m
  sorry

lemma exteriorPowerProdEquivProd_symm_apply_inr_ιMulti (i : ℕ) (m : Fin i → M) :
    (exteriorPowerProdEquivProd R M i).symm ⟨0, exteriorPower.ιMulti R i m⟩ =
      exteriorPower.ιMulti R (i + 1) (Fin.append ((LinearMap.inl R M R) ∘ m)
        ((LinearMap.inr R M R) ∘ ((LinearEquiv.funUnique (Fin 1) R R).symm 1))) := by
  sorry
