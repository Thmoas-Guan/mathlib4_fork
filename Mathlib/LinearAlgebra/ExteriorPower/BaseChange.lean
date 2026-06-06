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

/-- Helper for KoszulComplex baseChangeIso: the `S`-exterior algebra on `S ⊗[R] M`
is an `R`-scalar tower via the structure map `R → S`. -/
instance exteriorPowerBaseChange_exteriorAlgebra_isScalarTower :
    IsScalarTower R S (ExteriorAlgebra S (S ⊗[R] M)) :=
  IsScalarTower.of_algebraMap_eq (fun _ ↦ rfl)

lemma base_change_generator_map_update_add (i : ℕ) [DecidableEq (Fin i)] (m : Fin i → M)
    (j : Fin i) (x y : M) :
    (ExteriorAlgebra.ιMulti S i) (((mk R S M) 1) ∘ Function.update m j (x + y)) =
      (ExteriorAlgebra.ιMulti S i) (((mk R S M) 1) ∘ Function.update m j x) +
        (ExteriorAlgebra.ιMulti S i) (((mk R S M) 1) ∘ Function.update m j y) := by
  have hz (z : M) : ((TensorProduct.mk R S M 1) ∘ Function.update m j z) =
    Function.update (((TensorProduct.mk R S M 1) ∘ m)) j ((TensorProduct.mk R S M 1) z) := by
    funext a
    rcases eq_or_ne a j with rfl|ne
    · simp
    · simp [Function.update, ne]
  rw [hz (x + y), hz x, hz y, map_add, (ExteriorAlgebra.ιMulti S i).map_update_add]

lemma base_change_generator_map_update_smul (i : ℕ) [DecidableEq (Fin i)] (m : Fin i → M)
    (j : Fin i) (r : R) (x : M) :
    (ExteriorAlgebra.ιMulti S i) (((mk R S M) 1) ∘ Function.update m j (r • x)) =
      r • (ExteriorAlgebra.ιMulti S i) (((mk R S M) 1) ∘ Function.update m j x) := by
  have hz (z : M) : ((TensorProduct.mk R S M 1) ∘ Function.update m j z) =
    Function.update (((TensorProduct.mk R S M 1) ∘ m)) j ((TensorProduct.mk R S M 1) z) := by
    funext a
    rcases eq_or_ne a j with rfl|ne
    · simp
    · simp [Function.update, ne]
  rw [hz (r • x), hz x]
  simpa using (ExteriorAlgebra.ιMulti S i).map_update_smul
    (((TensorProduct.mk R S M 1) ∘ m)) j (algebraMap R S r) ((TensorProduct.mk R S M 1) x)

/-- Helper for KoszulComplex baseChangeIso: the generator-side alternating map
`m ↦ ιMulti_S (1 ⊗ m)` valued in the ambient `S`-exterior algebra, viewed as an `R`-module. -/
noncomputable def base_change_generator (i : ℕ) :
    M [⋀^Fin i]→ₗ[R] ExteriorAlgebra S (S ⊗[R] M) where
  toFun m :=
    ExteriorAlgebra.ιMulti S i ((TensorProduct.mk R S M 1) ∘ m)
  map_update_add' := base_change_generator_map_update_add R M S i
  map_update_smul' := base_change_generator_map_update_smul R M S i
  map_eq_zero_of_eq' m j k hjk hjk_ne := by
    have : (((mk R S M) 1) ∘ m) j = (((mk R S M) 1) ∘ m) k := by
      simpa [Function.comp] using congrArg ((TensorProduct.mk R S M 1)) hjk
    -- Equal coordinates after applying `1 ⊗ -` force the alternating expression to vanish.
    simpa [Function.comp] using (ExteriorAlgebra.ιMulti S i).map_eq_zero_of_eq
      (((TensorProduct.mk R S M 1) ∘ m)) this hjk_ne

/-- Helper for KoszulComplex baseChangeIso: the generator-side alternating map
`m ↦ ιMulti_S (1 ⊗ m)` cod-restricted to the fixed-degree summand. -/
noncomputable def base_change_generator_codrestrict (i : ℕ) :
    M [⋀^Fin i]→ₗ[R] ↥((⋀[S]^i (S ⊗[R] M)).restrictScalars R) :=
  (base_change_generator R M S i).codRestrict _ fun m =>
    -- The image of `ιMulti` already lies in the fixed-degree exterior-power summand.
    ExteriorAlgebra.ιMulti_range S i (Set.mem_range_self ((TensorProduct.mk R S M 1) ∘ m))

/-- Helper for KoszulComplex baseChangeIso: the forward linear map before upgrading
from the restricted-scalars target to the `S`-linear equivalence. -/
noncomputable def exteriorPower.baseChangeIsoForward (i : ℕ) :
    S ⊗[R] (⋀[R]^i M) →ₗ[S] ↥((⋀[S]^i (S ⊗[R] M)).restrictScalars R) :=
  -- Tensor-lift the `R`-linear map so the scalar on the left tensor factor acts on the target.
  TensorProduct.AlgebraTensorModule.lift {
    toFun s := s • exteriorPower.alternatingMapLinearEquiv
      (base_change_generator_codrestrict R M S i)
    map_add' s t := by simp [add_smul]
    map_smul' s t := by simp [smul_smul] }

/-- Helper for KoszulComplex baseChangeIso: the forward map sends the pure generator
`1 ⊗ ιMulti_R m` to `ιMulti_S (1 ⊗ m)`. -/
lemma baseChangeIso_forward_apply_one_tmul_ιMulti (i : ℕ) (m : Fin i → M) :
    exteriorPower.baseChangeIsoForward R M S i (1 ⊗ₜ[R] exteriorPower.ιMulti R i m) =
      ⟨exteriorPower.ιMulti S i ((TensorProduct.mk R S M 1) ∘ m),
        ExteriorAlgebra.ιMulti_range S i
          (Set.mem_range_self ((TensorProduct.mk R S M 1) ∘ m))⟩ := by
  rw [exteriorPower.baseChangeIsoForward, TensorProduct.AlgebraTensorModule.lift_tmul]
  simp only [LinearMap.coe_mk, AddHom.coe_mk, one_smul,
    exteriorPower.alternatingMapLinearEquiv_apply_ιMulti, exteriorPower.ιMulti_apply_coe]
  rfl

/-- Helper for KoszulComplex baseChangeIso: the degree-`i` projection out of the exterior algebra,
implemented by the `liftAlternating` family that is zero away from degree `i`. -/
noncomputable def exteriorPower.degreeProjection (i : ℕ) :
    ExteriorAlgebra R M →ₗ[R] (⋀[R]^i M) :=
  ExteriorAlgebra.liftAlternating (R := R) (M := M) (N := (⋀[R]^i M))
    (Function.update 0 i (exteriorPower.ιMulti R i))

/-- Helper for KoszulComplex baseChangeIso: the degree projection is the identity on
the canonical degree-`i` generator. -/
lemma exteriorPower.degreeProjection_apply_ιMulti (i : ℕ) (m : Fin i → M) :
    exteriorPower.degreeProjection R M i (ExteriorAlgebra.ιMulti R i m) =
      exteriorPower.ιMulti R i m := by
  -- `liftAlternating` returns the updated family on the matching degree.
  rw [exteriorPower.degreeProjection]
  simp

/-- Helper for KoszulComplex baseChangeIso: the tensor-side generator map
`s ⊗ m ↦ s ⊗ ι_R(m)` into the base-changed exterior algebra. -/
noncomputable def base_change_tensor_generator :
    S ⊗[R] M →ₗ[S] S ⊗[R] ExteriorAlgebra R M :=
  TensorProduct.AlgebraTensorModule.map (LinearMap.id : S →ₗ[S] S)
    (ExteriorAlgebra.ι R : M →ₗ[R] ExteriorAlgebra R M)

/-- Helper for KoszulComplex baseChangeIso: tensor generators anticommute in the
base-changed exterior algebra. -/
lemma base_change_tensor_generator_mul_add_swap (x y : S ⊗[R] M) :
    base_change_tensor_generator R M S x * base_change_tensor_generator R M S y +
      base_change_tensor_generator R M S y * base_change_tensor_generator R M S x = 0 := by
  -- Reduce the anticommutation relation to pure tensors in each variable.
  refine TensorProduct.induction_on x ?_ ?_ ?_
  · simp [base_change_tensor_generator]
  · intro s m
    refine TensorProduct.induction_on y ?_ ?_ ?_
    · simp [base_change_tensor_generator]
    · intro t n
      -- On pure tensors this is exactly the usual exterior-algebra anticommutation relation.
      simp [base_change_tensor_generator, Algebra.TensorProduct.tmul_mul_tmul,
        ExteriorAlgebra.ι_add_mul_swap, mul_comm, ← TensorProduct.tmul_add]
    · intro y₁ y₂ hy₁ hy₂
      -- Bilinearity turns the add case into the sum of the previously established identities.
      simpa [map_add, add_mul, mul_add, add_assoc, add_left_comm, add_comm] using
        congrArg₂ HAdd.hAdd hy₁ hy₂
  · intro x₁ x₂ hx₁ hx₂
    -- Bilinearity in the left input gives the final add case.
    simpa [map_add, add_mul, mul_add, add_assoc, add_left_comm, add_comm] using
      congrArg₂ HAdd.hAdd hx₁ hx₂

/-- Helper for KoszulComplex baseChangeIso: every tensor generator squares to zero in
the base-changed exterior algebra. -/
lemma base_change_tensor_generator_sq_zero (x : S ⊗[R] M) :
    base_change_tensor_generator R M S x * base_change_tensor_generator R M S x = 0 := by
  -- Check the square-zero relation by induction on the tensor and use the anticommutation lemma
  -- for the cross term in the add case.
  refine TensorProduct.induction_on x ?_ ?_ ?_
  · simp [base_change_tensor_generator]
  · intro s m
    simp [base_change_tensor_generator, Algebra.TensorProduct.tmul_mul_tmul]
  · intro x y hx hy
    simp only [map_add, mul_add, add_mul, add_left_comm, add_assoc]
    simp [hx, hy, base_change_tensor_generator_mul_add_swap R M S x y]

/-- Helper for KoszulComplex baseChangeIso: the ambient exterior-algebra map from
`ExteriorAlgebra S (S ⊗[R] M)` to `S ⊗[R] ExteriorAlgebra R M`. -/
noncomputable def base_change_exterior_to_tensor :
    ExteriorAlgebra S (S ⊗[R] M) →ₐ[S] S ⊗[R] ExteriorAlgebra R M :=
  ExteriorAlgebra.lift S
    ⟨base_change_tensor_generator R M S, base_change_tensor_generator_sq_zero R M S⟩

/-- Helper for KoszulComplex baseChangeIso: the inverse-side alternating map obtained by
passing through the ambient exterior algebra and then projecting to degree `i`. -/
noncomputable def base_change_inverse_alternating (i : ℕ) :
    (S ⊗[R] M) [⋀^Fin i]→ₗ[S] S ⊗[R] (⋀[R]^i M) :=
  ((TensorProduct.AlgebraTensorModule.map
      (LinearMap.id : S →ₗ[S] S)
      (exteriorPower.degreeProjection R M i)).comp
      (base_change_exterior_to_tensor R M S).toLinearMap).compAlternatingMap
    (ExteriorAlgebra.ιMulti S i)

/-- Helper for KoszulComplex baseChangeIso: the inverse-side alternating map sends a tuple of
pure tensors to the scalar product tensor the degree-`i` exterior generator. -/
lemma base_change_inverse_alternating_apply_tmul
    (i : ℕ) (s : Fin i → S) (m : Fin i → M) :
    base_change_inverse_alternating R M S i (fun j ↦ s j ⊗ₜ[R] m j) =
      (Finset.univ.prod fun j ↦ s j) ⊗ₜ[R] exteriorPower.ιMulti R i m := by
  -- Expand the ambient `ιMulti`, evaluate the lift on generators, and then project to degree `i`.
  simp only [base_change_inverse_alternating, LinearMap.comp_apply,
    LinearMap.compAlternatingMap_apply, AlgHom.toLinearMap_apply, ExteriorAlgebra.ιMulti_apply]
  have hprod : (List.ofFn fun j ↦ s j ⊗ₜ[R] ExteriorAlgebra.ι R (m j)).prod =
    (Finset.univ.prod fun j ↦ s j) ⊗ₜ[R] (List.ofFn fun j ↦ ExteriorAlgebra.ι R (m j)).prod := by
    induction i with
    | zero => simp [Algebra.TensorProduct.one_def]
    | succ i ih =>
      rw [List.ofFn_succ, List.ofFn_succ, List.prod_cons, List.prod_cons, ih]
      simp [Algebra.TensorProduct.tmul_mul_tmul, Fin.prod_univ_succ]
  rw [map_list_prod (base_change_exterior_to_tensor R M S)]
  have himages :
      List.map (base_change_exterior_to_tensor R M S)
          (List.ofFn fun j ↦ ExteriorAlgebra.ι S (s j ⊗ₜ[R] m j)) =
        List.ofFn fun j ↦ s j ⊗ₜ[R] ExteriorAlgebra.ι R (m j) := by
    ext j
    simp [base_change_exterior_to_tensor, base_change_tensor_generator]
  rw [himages]
  rw [hprod]
  rw [TensorProduct.AlgebraTensorModule.map_tmul]
  simpa [ExteriorAlgebra.ιMulti_apply] using
    congrArg (fun x ↦ (Finset.univ.prod fun j ↦ s j) ⊗ₜ[R] x)
      (exteriorPower.degreeProjection_apply_ιMulti R M i m)

/-- Helper for KoszulComplex baseChangeIso: the visible forward linear map with codomain
`⋀[S]^i (S ⊗[R] M)` after removing the restricted-scalars wrapper. -/
noncomputable def base_change_forward (i : ℕ) :
    S ⊗[R] (⋀[R]^i M) →ₗ[S] ⋀[S]^i (S ⊗[R] M) :=
  (Submodule.restrictScalarsEquiv
      (R := S) (S := R) (p := (⋀[S]^i (S ⊗[R] M)))).symm.toLinearMap.comp
    (exteriorPower.baseChangeIsoForward R M S i)

/-- Helper for KoszulComplex baseChangeIso: the linear map on the `i`th exterior power induced
by the inverse-side alternating map. -/
noncomputable def base_change_inverse (i : ℕ) :
    ⋀[S]^i (S ⊗[R] M) →ₗ[S] S ⊗[R] (⋀[R]^i M) :=
  exteriorPower.alternatingMapLinearEquiv (base_change_inverse_alternating R M S i)

/-- Helper for KoszulComplex baseChangeIso: the inverse-side map retracts the forward map. -/
lemma base_change_left_inverse (i : ℕ) :
    (base_change_inverse R M S i).comp (base_change_forward R M S i) = LinearMap.id := by
  -- Use the tensor-lift equivalence: an `S`-linear map out of `S ⊗[R] X` is determined by its
  -- curried form, and the latter is determined by the value at `1`.
  apply (TensorProduct.AlgebraTensorModule.lift.equiv R S S S _ _).symm.injective
  change TensorProduct.AlgebraTensorModule.curry
      ((base_change_inverse R M S i).comp (base_change_forward R M S i)) =
    TensorProduct.AlgebraTensorModule.curry LinearMap.id
  apply LinearMap.ext (fun s ↦ ?_)
  apply LinearMap.ext (fun x ↦ ?_)
  rw [show s = s • (1 : S) by simp]
  simp only [TensorProduct.AlgebraTensorModule.curry_apply, map_smul]
  -- The remaining `R`-linear statement on `⋀[R]^i M` is checked on the canonical generators.
  have hmk : (((base_change_inverse R M S i).comp
    (base_change_forward R M S i)).restrictScalars R).comp (TensorProduct.mk R S (⋀[R]^i M) 1) =
      TensorProduct.mk R S (⋀[R]^i M) 1 := by
    apply exteriorPower.linearMap_ext
    ext m
    -- Both sides agree on the canonical exterior generators.
    have hforward : base_change_forward R M S i (1 ⊗ₜ[R] exteriorPower.ιMulti R i m) =
      exteriorPower.ιMulti S i ((TensorProduct.mk R S M 1) ∘ m) := by
      simpa [base_change_forward] using!
        congrArg ((Submodule.restrictScalarsEquiv R S (p := (⋀[S]^i (S ⊗[R] M)))).symm)
          (baseChangeIso_forward_apply_one_tmul_ιMulti R M S i m)
    simp only [LinearMap.restrictScalars_comp, LinearMap.compAlternatingMap_apply,
      LinearMap.coe_comp, LinearMap.coe_restrictScalars, Function.comp_apply, mk_apply]
    rw [hforward, base_change_inverse, exteriorPower.alternatingMapLinearEquiv_apply_ιMulti]
    simpa [Finset.prod_const_one] using!
      base_change_inverse_alternating_apply_tmul R M S i (fun _ ↦ 1) m
  simpa using congrArg (fun t ↦ s • t) (LinearMap.congr_fun hmk x)

lemma base_change_right_inverse (i : ℕ) :
    (base_change_forward R M S i).comp (base_change_inverse R M S i) = LinearMap.id := by
  sorry

/-
/-- Helper for KoszulComplex baseChangeIso: the tensors `1 ⊗ m` span the base-changed module. -/
lemma tensorProduct_mk_one_span :
    Submodule.span S (Set.range (TensorProduct.mk R S M 1 : M →ₗ[R] S ⊗[R] M)) = ⊤ := by
  -- Every pure tensor is an `S`-multiple of a tensor of the form `1 ⊗ m`.
  apply top_unique
  intro x _
  refine TensorProduct.induction_on x (Submodule.zero_mem _) ?_ ?_
  · intro s m
    rw [show s ⊗ₜ[R] m = s • (((TensorProduct.mk R S M 1) m)) by
      simp [TensorProduct.smul_tmul']]
    exact Submodule.smul_mem _ s <| Submodule.subset_span (Set.mem_range_self m)
  · intro x y hx hy
    exact Submodule.add_mem _ hx hy

/-- Helper for KoszulComplex baseChangeIso: the visible forward map is surjective because it
contains the exterior generators arising from the spanning set `1 ⊗ M`. -/
lemma base_change_forward_surjective (i : ℕ) :
    Function.Surjective (base_change_forward R M S i) := by
  intro y
  let generators :
      Set (⋀[S]^i (S ⊗[R] M)) :=
    exteriorPower.ιMulti S i ''
      { a | Set.range a ⊆ Set.range (TensorProduct.mk R S M 1 : M →ₗ[R] S ⊗[R] M) }
  have hspan :
      Submodule.span S generators = ⊤ := by
    -- The codomain is spanned by exterior products of vectors from the spanning set `1 ⊗ M`.
    simpa [generators] using exteriorPower.ιMulti_span_of_span
      (R := S) (M := S ⊗[R] M) (n := i)
      (s := Set.range (TensorProduct.mk R S M 1 : M →ₗ[R] S ⊗[R] M))
      (tensorProduct_mk_one_span R M S)
  have hy : y ∈ Submodule.span S generators := by
    simp [hspan]
  have hyRange : y ∈ LinearMap.range (base_change_forward R M S i) := by
    refine Submodule.span_induction
      (p := fun z _ ↦ z ∈ LinearMap.range (base_change_forward R M S i))
      ?_ (Submodule.zero_mem _) ?_ ?_ hy
    · intro z hz
      rcases hz with ⟨a, ha, rfl⟩
      classical
      let m : Fin i → M := fun j => Classical.choose (ha (Set.mem_range_self j))
      have hm : a = (TensorProduct.mk R S M 1) ∘ m := by
        funext j
        exact (Classical.choose_spec (ha (Set.mem_range_self j))).symm
      refine LinearMap.mem_range.2 ⟨1 ⊗ₜ[R] exteriorPower.ιMulti R i m, ?_⟩
      simpa [base_change_forward, hm] using!
        congrArg ((Submodule.restrictScalarsEquiv R S (p := (⋀[S]^i (S ⊗[R] M)))).symm)
          (baseChangeIso_forward_apply_one_tmul_ιMulti R M S i m)
    · intro x z hx hz hxRange hzRange
      exact Submodule.add_mem _ hxRange hzRange
    · intro a x hx hxRange
      exact Submodule.smul_mem _ a hxRange
  exact LinearMap.mem_range.1 hyRange

/-- Helper for KoszulComplex baseChangeIso: the visible forward map is bijective. -/
lemma base_change_forward_bijective (i : ℕ) : Function.Bijective (base_change_forward R M S i) := by
  refine ⟨?_, base_change_forward_surjective R M S i⟩
  -- The explicit left inverse shows injectivity.
  have hleft : Function.LeftInverse (base_change_inverse R M S i)
    (base_change_forward R M S i) := by
    intro x
    exact LinearMap.congr_fun (base_change_left_inverse R M S i) x
  exact hleft.injective
-/

def exteriorPower.baseChangeIso (i : ℕ) : S ⊗[R] (⋀[R]^i M) ≃ₗ[S] ⋀[S]^i (S ⊗[R] M) := sorry

lemma exteriorPower.baseChangeIso_apply_tmul (i : ℕ) (m : Fin i → M) :
    exteriorPower.baseChangeIso R M S i (1 ⊗ₜ[R] (exteriorPower.ιMulti R i m)) =
    exteriorPower.ιMulti S i ((TensorProduct.mk R S M 1) ∘ m) := by
  sorry
