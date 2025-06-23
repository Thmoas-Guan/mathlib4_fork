/-
Copyright (c) 2025 Yongle Hu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongle Hu, Nailin Guan
-/
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Mathlib.RingTheory.Flat.Localization
import Mathlib.RingTheory.Regular.RegularSequence

/-!
# `RingTheory.Sequence.IsWeaklyRegular` is stable under flat base change

## Main results
* `RingTheory.Sequence.IsWeaklyRegular.of_flat_isBaseChange`: Let `R` be a commutative ring,
  `M` be an `R`-module, `S` be a flat `R`-algebra, `N` be the base change of `M` to `S`.
  If `[r₁, …, rₙ]` is a weakly regular `M`-sequence, then its image in `N` is a weakly regular
  `N`-sequence.
-/

open RingTheory.Sequence Pointwise Module TensorProduct

@[simp]
theorem Submodule.Quotient.mk_out {R M : Type*} [Ring R] [AddCommGroup M] [Module R M]
    {p : Submodule R M} (m : M ⧸ p) : Submodule.Quotient.mk (Quotient.out m) = m :=
  Quotient.out_eq m

section Flat

variable {R S M N : Type*} [CommRing R] [CommRing S] [Algebra R S] [Flat R S]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] [Module S N]
  [IsScalarTower R S N] {f : M →ₗ[R] N} (hf : IsBaseChange S f) (x : R)

/-- If `M` is isomorphic to `N` as `R`-modules, then `M/xM` is isomorphic to `N/xN`. -/
protected def QuotSMulTop.congr (e : M ≃ₗ[R] N) : QuotSMulTop x M ≃ₗ[R] QuotSMulTop x N :=
  Submodule.Quotient.equiv (x • ⊤) (x • ⊤) e <|
    (Submodule.map_pointwise_smul x _ e.toLinearMap).trans (by simp)

omit [Flat R S] [AddCommGroup N] [Module R N] [Module S N] [IsScalarTower R S N] hf in
theorem TensorProduct.tsmul_eq_smul_one_tuml (s : S) (m : M) : s ⊗ₜ[R] m = s • (1 ⊗ₜ[R] m) := by
  nth_rw 1 [show s = s • 1 from by simp]
  rfl

variable (S) (M) in
/-- Let `R` be a commutative ring, `M` be an `R`-module, `S` be an `R`-algebra, then
  `S ⊗[R] (M/xM)` is isomorphic to `(S ⊗[R] M)⧸x(S ⊗[R] M)` as `S`-modules. -/
noncomputable def tensorQuotSMulTopEquivQuotSMulTopAlgebraMapTensor :
    S ⊗[R] QuotSMulTop x M ≃ₗ[S] QuotSMulTop ((algebraMap R S) x) (S ⊗[R] M) :=
  let f : S ⊗[R] QuotSMulTop x M →ₗ[S] QuotSMulTop ((algebraMap R S) x) (S ⊗[R] M) := by
    apply LinearMap.liftBaseChange S ?_
    apply Submodule.mapQ (x • ⊤) ((algebraMap R S) x • ⊤) (TensorProduct.mk R S M 1) (fun _ ↦ ?_)
    simp only [Submodule.mem_smul_pointwise_iff_exists, Submodule.mem_top, true_and,
      Submodule.mem_comap, forall_exists_index]
    intro _ hm
    simp [← hm]
  let N : Submodule S (S ⊗[R] M) := (algebraMap R S) x • ⊤
  have hsm (s : S) (m : M) : N.mkQ (s ⊗ₜ[R] m) = f (s ⊗ₜ[R] Submodule.Quotient.mk m) := by
    simpa [tsmul_eq_smul_one_tuml s m] using by rfl
{ __ := f
  invFun m := LinearMap.lTensor S (Submodule.mkQ (x • ⊤)) (Quotient.out m)
  left_inv := by
    intro m
    have h : (LinearMap.lsmul R (S ⊗[R] QuotSMulTop x M)) x = 0 := by
      apply TensorProduct.ext
      ext s m
      simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.compr₂_apply, mk_apply,
        LinearMap.lsmul_apply, LinearMap.zero_apply]
      rw [← tmul_smul, show x • _ = (0 : QuotSMulTop x M) from
          (Submodule.Quotient.mk_eq_zero _).mpr (Submodule.smul_mem_pointwise_smul m x ⊤ trivial)]
      exact tmul_zero _ s
    have hx (m : S ⊗[R] QuotSMulTop x M) : x • m = 0 := congrFun (congrArg DFunLike.coe h) m
    induction' m with s m m₁ m₂
    · obtain ⟨b, _, h⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp <|
        (Submodule.Quotient.mk_eq_zero N).mp (Quotient.out_eq (0 : _ ⧸ N))
      simp [← h, hx]
    · have hsm : _ = f (s ⊗ₜ[R] m) := (hsm s (Quotient.out m)).trans (by simp)
      obtain ⟨b, _, h⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp <|
        (Submodule.Quotient.eq' N).mp (hsm.trans (Quotient.out_eq _).symm)
      simp only [← add_eq_of_eq_sub <| h.trans (neg_add_eq_sub _ _), hx, LinearMap.coe_toAddHom,
        AddHom.toFun_eq_coe, algebraMap_smul, map_add, map_smul, LinearMap.lTensor_tmul, zero_add]
      congr 1
      exact Quotient.out_eq m
    · have hm : N.mkQ (Quotient.out (f m₁ + f m₂)) =
        N.mkQ (Quotient.out (f m₁) + Quotient.out (f m₂)) := by simp
      obtain ⟨b, _, h⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp <|
        (Submodule.Quotient.eq' N).mp hm.symm
      simpa [← add_eq_of_eq_sub <| h.trans (neg_add_eq_sub _ _), hx] using by congr 1
  right_inv := by
    intro m
    simp only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom]
    nth_rw 2 [← Submodule.Quotient.mk_out m]
    induction Quotient.out m
    · simp
    · simp [← hsm]
    · simpa using by congr 1 }

include hf

variable {x} in
theorem IsSMulRegular.of_flat_isBaseChange (reg : IsSMulRegular M x) :
    IsSMulRegular N (algebraMap R S x) := by
  have eq : hf.lift (f ∘ₗ (LinearMap.lsmul R M) x) = (LinearMap.lsmul S N) (algebraMap R S x) :=
    hf.algHom_ext _ _ (fun _ ↦ by simp [hf.lift_eq])
  convert Module.Flat.isBaseChange_preserves_injective_linearMap hf hf ((LinearMap.lsmul R M) x) reg
  rw [eq]
  rfl

/-- Let `R` be a commutative ring, `M` be an `R`-module, `S` be a flat `R`-algebra, `N` be the base
  change of `M` to `S`. If `[r₁, …, rₙ]` is a weakly regular `M`-sequence, then its image in `N` is
  a weakly regular `N`-sequence. -/
theorem RingTheory.Sequence.IsWeaklyRegular.of_flat_isBaseChange {rs : List R}
    (reg : IsWeaklyRegular M rs) : IsWeaklyRegular N (rs.map (algebraMap R S)) := by
  generalize len : rs.length = n
  induction' n with n ih generalizing M N rs
  · simp [List.length_eq_zero_iff.mp len]
  · match rs with
    | [] => simp at len
    | x :: rs' =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at len
      simp only [isWeaklyRegular_cons_iff, List.map_cons] at reg ⊢
      have e := tensorQuotSMulTopEquivQuotSMulTopAlgebraMapTensor S M x ≪≫ₗ
        QuotSMulTop.congr ((algebraMap R S) x) hf.equiv
      have hg : IsBaseChange S <|
          e.toLinearMap.restrictScalars R ∘ₗ TensorProduct.mk R S (QuotSMulTop x M) 1 :=
        IsBaseChange.of_equiv e (fun _ ↦ by simp)
      exact ⟨reg.1.of_flat_isBaseChange hf, ih hg reg.2 len⟩

end Flat

section FaithfullyFlat

variable {R S M N P : Type*} [CommRing R] [CommRing S] [Algebra R S] [FaithfullyFlat R S]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] [Module S N]
  [IsScalarTower R S N] {f : M →ₗ[R] N} (hf : IsBaseChange S f) (x : R)
  (P : Type*) [AddCommGroup P] [Module R P] [Module S P] [IsScalarTower R S P]

variable (R S M) in
/-- `(S ⊗[R] M) ⊗[S] P ≃ₗ[R] M ⊗[R] P`. -/
noncomputable def baseChangeTensorEquiv : (S ⊗[R] M) ⊗[S] P ≃ₗ[R] M ⊗[R] P :=
  (TensorProduct.comm S _ P).restrictScalars R ≪≫ₗ
    ((TensorProduct.AlgebraTensorModule.assoc R S S P S M).restrictScalars R).symm ≪≫ₗ
      LinearEquiv.rTensor M ((TensorProduct.rid S P).restrictScalars R) ≪≫ₗ TensorProduct.comm R P M

variable (S) in
/-- `S ⧸ IS ≃ₗ[R] S ⊗[R] (R ⧸ I)`. -/
noncomputable def Ideal.qoutMapEquivTensorQout {I : Ideal R} :
    (S ⧸ Ideal.map (algebraMap R S) I) ≃ₗ[R] S ⊗[R] (R ⧸ I) :=
  LinearEquiv.symm <| tensorQuotEquivQuotSMul S I ≪≫ₗ Submodule.quotEquivOfEq _ _ (by simp) ≪≫ₗ
    Submodule.Quotient.restrictScalarsEquiv R _

/-- `(S ⊗[R] M) ⧸ I(S ⊗[R] M) ≃ₗ[R] S ⊗[R] (M ⧸ IM)`. -/
noncomputable def TensorProduct.quotMapSMulEquivTensorQuot (I : Ideal R) :
    ((S ⊗[R] M) ⧸ I.map (algebraMap R S) • (⊤ : Submodule S (S ⊗[R] M))) ≃ₗ[R]
    S ⊗[R] (M ⧸ (I • (⊤ : Submodule R M))) :=
  ((tensorQuotEquivQuotSMul (S ⊗[R] M) (I.map (algebraMap R S))).restrictScalars R).symm ≪≫ₗ
    baseChangeTensorEquiv R S M _ ≪≫ₗ  LinearEquiv.lTensor M (I.qoutMapEquivTensorQout S) ≪≫ₗ
      leftComm R M S _ ≪≫ₗ LinearEquiv.lTensor S (tensorQuotEquivQuotSMul M I)

include hf

variable (R S M) in
/-- Let `R` be a commutative ring, `S` be an `R`-algebra, `M` be an `R`-module, `P` be an `S`
  module, `N` be the base change of `M` to `S`, then `P ⊗[S] N` is isomorphic to `P ⊗[R] M`
  as `S`-modules. -/
noncomputable def isBaseChangeTensorEquiv : N ⊗[S] P ≃ₗ[R] M ⊗[R] P :=
  (LinearEquiv.rTensor P hf.equiv.symm).restrictScalars R ≪≫ₗ baseChangeTensorEquiv R S M P

/-- Let `R` be a commutative ring, `S` be an `R`-algebra, `I` is be ideal of `R`, `N` be the base
  change of `M` to `S`, then `N ⧸ IN` is isomorphic to `S ⊗[R] (M ⧸ IM)` as `S` modules. -/
noncomputable def IsBaseChange.quotMapSMulEquivTensorQuot (I : Ideal R) :
    (N ⧸ I.map (algebraMap R S) • (⊤ : Submodule S N)) ≃ₗ[R]
    S ⊗[R] (M ⧸ (I • (⊤ : Submodule R M))) :=
  ((tensorQuotEquivQuotSMul N (I.map (algebraMap R S))).restrictScalars R).symm ≪≫ₗ
    isBaseChangeTensorEquiv R S M hf _ ≪≫ₗ  LinearEquiv.lTensor M (I.qoutMapEquivTensorQout S) ≪≫ₗ
      leftComm R M S _ ≪≫ₗ LinearEquiv.lTensor S (tensorQuotEquivQuotSMul M I)

theorem Module.FaithfullyFlat.smul_top_ne_top_of_isBaseChange {I : Ideal R}
    (h : I • (⊤ : Submodule R M) ≠ ⊤) : I.map (algebraMap R S) • (⊤ : Submodule S N) ≠ ⊤ := by
  intro eq
  have := Submodule.subsingleton_quotient_iff_eq_top.mpr eq
  have := (hf.quotMapSMulEquivTensorQuot I).symm.subsingleton
  have : Subsingleton (M ⧸ (I • (⊤ : Submodule R M))) := lTensor_reflects_triviality R S _
  exact not_nontrivial _ (Submodule.Quotient.nontrivial_of_lt_top (I • ⊤) h.lt_top)

/-- Let `R` be a commutative ring, `M` be an `R`-module, `S` be a faithfully flat `R`-algebra,
  `N` be the base change of `M` to `S`. If `[r₁, …, rₙ]` is a regular `M`-sequence, then its image
  in `N` is a regular `N`-sequence. -/
theorem RingTheory.Sequence.IsRegular.of_faithfullyFlat_isBaseChange {rs : List R}
    (reg : IsRegular M rs) : IsRegular N (rs.map (algebraMap R S)) := by
  refine ⟨reg.1.of_flat_isBaseChange hf, ?_⟩
  rw [← Ideal.map_ofList]
  exact (FaithfullyFlat.smul_top_ne_top_of_isBaseChange hf reg.2.symm).symm

end FaithfullyFlat

section IsLocalizedModule

variable {R : Type*} [CommRing R] (S : Submonoid R)
  (R' : Type*) [CommRing R'] [Algebra R R'] [IsLocalization S R']
  {M : Type*} [AddCommGroup M] [Module R M]
  {M' : Type*} [AddCommGroup M'] [Module R M'] [Module R' M'] [IsScalarTower R R' M']
  (f : M →ₗ[R] M') [IsLocalizedModule S f] {x : R} {rs : List R}

include S f

theorem IsSMulRegular.of_isLocalizedModule (reg : IsSMulRegular M x) :
    IsSMulRegular M' (algebraMap R R' x) :=
  have : Flat R R' := IsLocalization.flat R' S
  reg.of_flat_isBaseChange (IsLocalizedModule.isBaseChange S R' f)

theorem RingTheory.Sequence.IsWeaklyRegular.of_isLocalizedModule
    (reg : IsWeaklyRegular M rs) : IsWeaklyRegular M' (rs.map (algebraMap R R')) :=
  have : Flat R R' := IsLocalization.flat R' S
  reg.of_flat_isBaseChange (IsLocalizedModule.isBaseChange S R' f)

end IsLocalizedModule

section AtPrime

theorem RingTheory.Sequence.IsWeaklyRegular.isRegular_of_isLocalizedModule_of_mem_prime
    {R : Type*} [CommRing R] (p : Ideal R) [p.IsPrime] (Rₚ : Type*) [CommRing Rₚ] [Algebra R Rₚ]
    [IsLocalization.AtPrime Rₚ p]
    {M Mₚ : Type*} [AddCommGroup M] [Module R M] [Nontrivial Mₚ] [AddCommGroup Mₚ] [Module Rₚ Mₚ]
    [Module.Finite Rₚ Mₚ] [Module R Mₚ] [IsScalarTower R Rₚ Mₚ]
    (f : M →ₗ[R] Mₚ) [IsLocalizedModule.AtPrime p f] {rs : List R} (reg : IsWeaklyRegular M rs)
    (mem : ∀ r ∈ rs, r ∈ p) : IsRegular Mₚ (rs.map (algebraMap R Rₚ)) := by
  have : IsLocalRing Rₚ := IsLocalization.AtPrime.isLocalRing Rₚ p
  refine (IsLocalRing.isRegular_iff_isWeaklyRegular_of_subset_maximalIdeal ?_).mpr <|
    reg.of_isLocalizedModule p.primeCompl Rₚ f
  intro _ hr
  rcases List.mem_map.mp hr with ⟨r, hr, eq⟩
  simpa only [← eq, IsLocalization.AtPrime.to_map_mem_maximal_iff Rₚ p] using mem r hr

end AtPrime
