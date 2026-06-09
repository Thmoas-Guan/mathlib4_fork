/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.LinearAlgebra.ExteriorAlgebra.Grading
public import Mathlib.LinearAlgebra.ExteriorPower.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Graded.Internal

/-!

# Exterior algebra of product module

-/

@[expose] public section

universe u

variable (R : Type u) [CommRing R]

variable (M N : Type*) [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

open TensorProduct

namespace ExteriorAlgebra

noncomputable def prodEquivTensorForwardAux :
    (M × N) →ₗ[R] ((fun (i : ℕ) => ⋀[R]^i M) ᵍ⊗[R] (fun (i : ℕ) => ⋀[R]^i N)) :=
  (GradedTensorProduct.includeLeft _ _).toLinearMap.comp ((ι R).comp (LinearMap.fst R M N)) +
    (GradedTensorProduct.includeRight _ _).toLinearMap.comp ((ι R).comp (LinearMap.snd R M N))

variable {M N} in
lemma prodEquivTensorForwardAux_apply_mul (m : M × N) :
    (prodEquivTensorForwardAux R M N) m * (prodEquivTensorForwardAux R M N) m = 0 := by

  sorry

noncomputable def prodEquivTensorForward :
    ExteriorAlgebra R (M × N) →ₐ[R] ((fun (i : ℕ) => ⋀[R]^i M) ᵍ⊗[R] (fun (i : ℕ) => ⋀[R]^i N)) :=
  ExteriorAlgebra.lift R ⟨prodEquivTensorForwardAux R M N, prodEquivTensorForwardAux_apply_mul R⟩

variable {M N} in
lemma map_inl_inr_anticomm (i j : ℕ) (a : ⋀[R]^i M) (b : ⋀[R]^j N) :
    (map (LinearMap.inl R M N)) a * (map (LinearMap.inr R M N)) b =
      (-1) ^ (j * i) • ((map (LinearMap.inr R M N)) b * (map (LinearMap.inl R M N)) a) := by
  have amem : a.1 ∈ ⋀[R]^i M := a.2
  have bmem : b.1 ∈ ⋀[R]^j N := b.2
  rw [← (Submodule.ext_iff.mp (ιMulti_span_fixedDegree R _))] at amem bmem
  refine Submodule.span_induction₂ (p := fun x y hx hy ↦
    (map (LinearMap.inl R M N)) x * (map (LinearMap.inr R M N)) y =
      (-1) ^ (j * i) • ((map (LinearMap.inr R M N)) y * (map (LinearMap.inl R M N)) x))
        ?_ ?_ ?_ ?_ ?_ ?_ ?_ amem bmem
  · rintro x y ⟨mx, rfl⟩ ⟨my, rfl⟩

    sorry
  all_goals simp +contextual [add_mul, mul_add]

noncomputable def prodEquivTensorInverse :
    ((fun (i : ℕ) => ⋀[R]^i M) ᵍ⊗[R] (fun (i : ℕ) => ⋀[R]^i N)) →ₐ[R] ExteriorAlgebra R (M × N) :=
  GradedTensorProduct.lift _ _ (ExteriorAlgebra.map (LinearMap.inl R M N))
    (ExteriorAlgebra.map (LinearMap.inr R M N)) (map_inl_inr_anticomm R)

lemma prodEquivTensor_inverse_comp_forward :
    (prodEquivTensorInverse R M N).comp (prodEquivTensorForward R M N) = AlgHom.id R _ := by
  sorry

lemma prodEquivTensor_forward_comp_inverse :
    (prodEquivTensorForward R M N).comp (prodEquivTensorInverse R M N) = AlgHom.id R _ := by
  sorry

noncomputable def prodEquivTensor :
    ExteriorAlgebra R (M × N) ≃ₐ[R]
      ((fun (i : ℕ) => ⋀[R]^i M) ᵍ⊗[R] (fun (i : ℕ) => ⋀[R]^i N)) where
  __ := prodEquivTensorForward R M N
  invFun := prodEquivTensorInverse R M N
  left_inv x := AlgHom.congr_fun (prodEquivTensor_inverse_comp_forward R M N) x
  right_inv x := AlgHom.congr_fun (prodEquivTensor_forward_comp_inverse R M N) x

lemma prodEquivTensor_symm_apply_tmul_ιMulti (i j : ℕ) (m : Fin i → M) (n : Fin j → N) :
    (prodEquivTensor R M N).symm (ιMulti R i m ᵍ⊗ₜ[R] ιMulti R j n) =
      ιMulti R (i + j) (Fin.append (LinearMap.inl R M N ∘ m) (LinearMap.inr R M N ∘ n)) := by
  simp [prodEquivTensor, prodEquivTensorInverse, ExteriorAlgebra.ιMulti_mul_ιMulti]

end ExteriorAlgebra
