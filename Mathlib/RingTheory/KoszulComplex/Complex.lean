/-
Copyright (c) 2026 Jingting Wang, Nailin Guan, Yi Yuan, Yongle Hu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jingting Wang, Nailin Guan, Yi Yuan, Yongle Hu
-/
module

public import Mathlib.RingTheory.KoszulComplex.Preliminaries
public import Mathlib.RingTheory.KoszulComplex.ExteriorAlgebraProduct
public import Mathlib.RingTheory.KoszulComplex.ExteriorPowerProduct
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.ExteriorPower
public import Mathlib.Algebra.Homology.Augment
public import Mathlib.Algebra.Homology.HomologySequence
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Module.SpanRank
public import Mathlib.LinearAlgebra.ExteriorPower.Basis
public import Mathlib.RingTheory.Regular.RegularSequence
public import Mathlib.LinearAlgebra.Alternating.Uncurry.Fin

/-!
# Definition of Koszul complex
-/

@[expose] public section

universe u v

open CategoryTheory Category MonoidalCategory Limits Module ExteriorAlgebra

variable {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M] (φ : M →ₗ[R] R)

/-- The alternating map on `(n + 1)`-tuples whose induced linear map is the Koszul differential. -/
noncomputable def koszulComplexAuxAlternating (n : ℕ) :
    M [⋀^Fin (n + 1)]→ₗ[R] ⋀[R]^n M :=
  AlternatingMap.alternatizeUncurryFin (φ.smulRight (exteriorPower.ιMulti R n))

lemma koszulComplexAuxAlternating_apply (n : ℕ) (x : Fin (n + 1) → M) :
    koszulComplexAuxAlternating φ n x =
      ∑ i : Fin (n + 1),
        ((-1 : R) ^ (i : ℕ) * φ (x i)) • exteriorPower.ιMulti R n (i.removeNth x) := by
  rw [koszulComplexAuxAlternating, AlternatingMap.alternatizeUncurryFin_apply]
  refine Finset.sum_congr rfl ?_
  intro i _
  have hremove : x ∘ i.succAbove = i.removeNth x := rfl
  simp [LinearMap.smulRight_apply, AlternatingMap.smul_apply, ← hremove,
    ← Int.cast_smul_eq_zsmul R, smul_smul]

/-- The auxiliary differential used to build the Koszul complex. -/
noncomputable def koszulComplexAux (n : ℕ) : ⋀[R]^(n + 1) M →ₗ[R] ⋀[R]^n M :=
  exteriorPower.alternatingMapLinearEquiv (koszulComplexAuxAlternating (R := R) (M := M) φ n)

lemma koszulComplexAux_comp_eq_zero (n : ℕ) :
    koszulComplexAux φ n ∘ₗ koszulComplexAux φ (n + 1) = 0 := by
  let β : M →ₗ[R] M →ₗ[R] M [⋀^Fin n]→ₗ[R] ⋀[R]^n M :=
    φ.smulRight (φ.smulRight (exteriorPower.ιMulti R n))
  have hβ : ∀ x y, β x y = β y x := by
    intro x y
    ext v
    simp [β, smul_smul, mul_comm]
  -- Unfold the concrete Koszul composite into the twice-uncurried alternating construction.
  have hcomp :
      (koszulComplexAux φ n).compAlternatingMap (koszulComplexAuxAlternating φ (n + 1)) =
        AlternatingMap.alternatizeUncurryFin (AlternatingMap.alternatizeUncurryFinLM ∘ₗ β) := by
    ext v
    simp [koszulComplexAux, koszulComplexAuxAlternating, β,
      AlternatingMap.alternatizeUncurryFin_apply, Finset.smul_sum, map_sum, smul_smul]
  -- Transport the linear-map composite to the alternating-map side,
  -- where the symmetry theorem applies directly.
  rw [show koszulComplexAux φ (n + 1) =
      exteriorPower.alternatingMapLinearEquiv (koszulComplexAuxAlternating φ (n + 1)) by rfl]
  rw [← exteriorPower.alternatingMapLinearEquiv_comp]
  rw [LinearEquiv.map_eq_zero_iff]
  rw [hcomp]
  exact AlternatingMap.alternatizeUncurryFin_alternatizeUncurryFinLM_comp_of_symmetric hβ

set_option backward.isDefEq.respectTransparency false in
noncomputable def koszulComplex : ChainComplex (ModuleCat R) ℕ :=
  ChainComplex.of
    (ModuleCat.of R M).exteriorPower
    (fun n ↦ ModuleCat.ofHom (koszulComplexAux φ n))
    (fun n ↦ by simp [← ModuleCat.ofHom_comp, koszulComplexAux_comp_eq_zero])

lemma koszulComplex.X_eq_exteriorPower (i : ℕ) :
    (koszulComplex φ).X i = ModuleCat.of R (⋀[R]^i M) := rfl

lemma koszulComplex.d_eq_aux (i : ℕ) :
    (koszulComplex φ).d (i + 1) i = ModuleCat.ofHom (koszulComplexAux φ i) := by
  simp [koszulComplex]

section DifferentialGradedAlgebra

end DifferentialGradedAlgebra

namespace koszulComplex

variable {N : Type v} [AddCommGroup N] [Module R N]

noncomputable def ofList (l : List R) := koszulComplex (Fintype.linearCombination R l.get)

section functoriality

lemma mapAuxAlternating_apply (f : M →ₗ[R] N) (φ' : N →ₗ[R] R) (h : φ' ∘ₗ f = φ)
    (i : ℕ) (v : Fin (i + 1) → M) :
    ((koszulComplexAuxAlternating φ' i) (f ∘ v) : ⋀[R]^i N) =
      exteriorPower.map i f ((koszulComplexAuxAlternating φ i) v) := by
  calc
    _ = ∑ x : Fin (i + 1), (-1) ^ (x : ℕ) • φ' (f (v x)) •
          exteriorPower.ιMulti R i (x.removeNth (f ∘ v)) := by
      simp [koszulComplexAuxAlternating, AlternatingMap.alternatizeUncurryFin_apply]
    _ = ∑ x : Fin (i + 1), (-1) ^ (x : ℕ) • φ (v x) •
          exteriorPower.ιMulti R i (f ∘ x.removeNth v) := by
      refine Finset.sum_congr rfl (fun x hx ↦ ?_)
      simp only [← h, LinearMap.coe_comp, Function.comp_apply]
      rfl
    _ = exteriorPower.map i f ((koszulComplexAuxAlternating φ i) v) := by
      rw [koszulComplexAuxAlternating, AlternatingMap.alternatizeUncurryFin_apply]
      simp [map_sum, map_smul, exteriorPower.map_apply_ιMulti]

lemma map_aux_comm (f : M →ₗ[R] N) (φ' : N →ₗ[R] R) (h : φ' ∘ₗ f = φ) (i : ℕ) :
    ModuleCat.ofHom (exteriorPower.map (i + 1) f) ≫ ModuleCat.ofHom (koszulComplexAux φ' i) =
      ModuleCat.ofHom (koszulComplexAux φ i) ≫ ModuleCat.ofHom (exteriorPower.map i f) := by
  ext v
  simp [koszulComplexAux, mapAuxAlternating_apply (φ := φ) (f := f) (φ' := φ') h]

noncomputable def map (f : M →ₗ[R] N) (φ' : N →ₗ[R] R) (h : φ' ∘ₗ f = φ) :
    koszulComplex φ ⟶ koszulComplex φ' :=
  ChainComplex.ofHom
    (fun i ↦ ModuleCat.ofHom (exteriorPower.map i f))
    (fun i ↦ by simpa [d_eq_aux] using! map_aux_comm φ f φ' h i)

variable {L : Type v} [AddCommGroup L] [Module R L]

variable {φ} in
lemma map_comp_condition {f : M →ₗ[R] N} {φ' : N →ₗ[R] R} {g : N →ₗ[R] L} {φ'' : L →ₗ[R] R}
    (h : φ' ∘ₗ f = φ) (h' : φ'' ∘ₗ g = φ') : φ'' ∘ₗ (g ∘ₗ f) = φ := by
  simp [← h, ← h', LinearMap.comp_assoc]

lemma map_comp (f : M →ₗ[R] N) (φ' : N →ₗ[R] R) (g : N →ₗ[R] L) (φ'' : L →ₗ[R] R)
    (h : φ' ∘ₗ f = φ) (h' : φ'' ∘ₗ g = φ') :
    koszulComplex.map φ f φ' h ≫ koszulComplex.map φ' g φ'' h' =
      koszulComplex.map φ (g ∘ₗ f) φ'' (map_comp_condition h h') := by
  ext i x
  simp [map, X_eq_exteriorPower, exteriorPower.map_comp]

noncomputable def isoOfEquiv (f : M ≃ₗ[R] N) (φ' : N →ₗ[R] R) (h : φ' ∘ₗ f = φ) :
    koszulComplex φ ≅ koszulComplex φ' where
  hom := koszulComplex.map φ f φ' h
  inv := koszulComplex.map φ' f.symm φ ((f.comp_toLinearMap_symm_eq φ' φ).mpr h.symm)
  hom_inv_id := by
    ext i x
    simp [map, X_eq_exteriorPower, ← exteriorPower.map_comp]
  inv_hom_id := by
    ext i x
    simp [map, X_eq_exteriorPower, ← exteriorPower.map_comp]

end functoriality

section specialX

noncomputable def XZeroLinearEquivRing : (koszulComplex φ).X 0 ≃ₗ[R] R :=
  exteriorPower.zeroEquiv R M

set_option backward.isDefEq.respectTransparency false in
lemma X_isZero_of_card_generators_lt {ι : Type*} [Finite ι] [LinearOrder ι] (g : ι → M)
    (hg : Submodule.span R (Set.range g) = ⊤) (i : ℕ) (hi : Nat.card ι < i) :
    IsZero ((koszulComplex φ).X i) :=
  ModuleCat.isZero_of_iff_subsingleton.mpr (subsingleton_of_card_generators_le R M g hg i hi)

lemma ofList_X_isZero_of_length_lt (l : List R) (i : ℕ) (hi : l.length < i) :
    IsZero ((ofList l).X i) :=
  X_isZero_of_card_generators_lt _ (Pi.basisFun R (Fin l.length))
    (Pi.basisFun R (Fin l.length)).span_eq i
      (by simpa [Nat.card_eq_fintype_card] using hi)

end specialX

section induction

variable (φ : M →ₗ[R] R) (a : R)

abbrev appendMap : M × R →ₗ[R] R := φ.comp (LinearMap.fst R M R) + a • (LinearMap.snd R M R)

variable (R M) in
noncomputable abbrev X_equiv_zero : ⋀[R]^0 M ≃ₗ[R] ⋀[R]^0 (M × R):=
  (exteriorPower.zeroEquiv R _).trans (exteriorPower.zeroEquiv R _).symm

lemma koszulComplexAux_eq_zero :
    (koszulComplexAux (appendMap φ a) 0).comp (exteriorPowerProdEquivProd R M 0).toLinearMap =
      (X_equiv_zero R M).toLinearMap.comp ((koszulComplexAux φ 0).comp (LinearMap.fst R _ _) +
        a • (LinearMap.snd R _ _)) := by
  ext m
  · sorry
  · sorry

variable (n : ℕ)

lemma koszulComplexAux_eq_pos (n : ℕ) :
    (koszulComplexAux (appendMap φ a) (n + 1)).comp
      (exteriorPowerProdEquivProd R M (n + 1)).toLinearMap =
        (exteriorPowerProdEquivProd R M n).toLinearMap.comp
          ((LinearMap.inl R _ _).comp ((koszulComplexAux φ (n + 1)).comp (LinearMap.fst R _ _)) +
            (LinearMap.inr R _ _).comp ((koszulComplexAux φ n).comp (LinearMap.snd R _ _)) +
              (-1 : ℤ) ^ (n + 1) • a • (LinearMap.inl R _ _).comp (LinearMap.snd R _ _)) := by
  ext m
  · sorry
  · sorry

noncomputable def from_ofList_hom_zero :
    (koszulComplex φ).X 0 ⟶ (koszulComplex (appendMap φ a)).X 0 :=
  ModuleCat.ofHom (X_equiv_zero R M).toLinearMap

noncomputable def from_ofList_hom_pos (i : ℕ) :
    (koszulComplex φ).X (i + 1) ⟶ (koszulComplex (appendMap φ a)).X (i + 1) :=
  ModuleCat.ofHom ((exteriorPowerProdEquivProd R M i).toLinearMap.comp (LinearMap.inl R _ _))

lemma from_ofList_hom_comm_zero :
    from_ofList_hom_pos φ a 0 ≫ (koszulComplex (appendMap φ a)).d (0 + 1) 0 =
    (koszulComplex φ).d (0 + 1) 0 ≫ from_ofList_hom_zero φ a := by
  ext y
  sorry

lemma from_ofList_hom_comm_pos (i : ℕ) :
    from_ofList_hom_pos φ a (i + 1) ≫ (koszulComplex (appendMap φ a)).d (i + 1 + 1) (i + 1) =
      (koszulComplex φ).d (i + 1 + 1) (i + 1) ≫ from_ofList_hom_pos φ a i := by
  ext y
  sorry

noncomputable def toAppendMap :
    koszulComplex φ ⟶ koszulComplex (appendMap φ a) :=
  ChainComplex.ofHom
    (fun i ↦
      match i with
      | 0 => from_ofList_hom_zero φ a
      | i + 1 => from_ofList_hom_pos φ a i)
    (fun i ↦
      match i with
      | 0 => from_ofList_hom_comm_zero φ a
      | i + 1 => from_ofList_hom_comm_pos φ a i)

noncomputable abbrev upOne : ChainComplex (ModuleCat R) ℕ :=
  (koszulComplex φ).augment (X := ModuleCat.of R PUnit) 0 (by simp)

/--
The canonical isomorphism of homology for augumenting with zero object.
May need to construct by cases whether `i = 0`.
-/
noncomputable abbrev upOneHomologyIso (i : ℕ) :
    (upOne φ).homology (i + 1) ≅ (koszulComplex φ).homology i := sorry

noncomputable def toUpOneHom (i : ℕ) :
    (koszulComplex (appendMap φ a)).X (i + 1) ⟶ (upOne φ).X (i + 1) :=
  ModuleCat.ofHom ((LinearMap.snd R _ _).comp (exteriorPowerProdEquivProd R M i).symm.toLinearMap)

lemma to_self_hom_comm (i : ℕ) :
    toUpOneHom φ a (i + 1) ≫ (koszulComplex φ).d (i + 1) i =
      (koszulComplex (appendMap φ a)).d (i + 1 + 1) (i + 1) ≫ toUpOneHom φ a i := by
  ext y
  sorry

noncomputable def toUpOne :
    koszulComplex (appendMap φ a) ⟶ upOne φ :=
  ChainComplex.ofHom
    (fun i ↦
      match i with
      | 0 => 0
      | i + 1 => toUpOneHom φ a i)
    (fun i ↦
      match i with
      | 0 => by
        simp only [Nat.reduceAdd, ChainComplex.augment_X_zero, ChainComplex.augment_X_succ,
          ChainComplex.augment_d_one_zero, comp_zero]
        exact comp_zero.symm
      | i + 1 => to_self_hom_comm φ a i)

lemma toAppendMap_comp_toUpOne_eq_zero :
    toAppendMap φ a ≫ toUpOne φ a = 0 := by
  sorry

noncomputable def shortComplexProd : ShortComplex (ChainComplex (ModuleCat R) ℕ) where
  f := toAppendMap φ a
  g := toUpOne φ a
  zero := toAppendMap_comp_toUpOne_eq_zero φ a

noncomputable def shortComplexProd_shortExact : (shortComplexProd φ a).ShortExact where
  exact := sorry
  mono_f := sorry
  epi_g := sorry

lemma shortComplexProd_δ_eq (i : ℕ) :
    (shortComplexProd_shortExact φ a).δ (i + 1) i rfl =
      ((-1 : R) ^ i * a) • (upOneHomologyIso φ i).hom := by
  sorry

end induction

section H0

variable (φ : M →ₗ[R] R)

noncomputable def zeroHomologyLinearEquivAux : (koszulComplex φ).homology 0 ≃ₗ[R]
    (⋀[R]^0 M) ⧸ (koszulComplexAux φ 0).range :=
  (((koszulComplex φ).isoHomologyι₀.trans
    ((koszulComplex φ).opcyclesIsoSc' 1 0 0 (by simp) (by simp))).trans
      ((koszulComplex φ).sc' 1 0 0).moduleCatOpcyclesIso).toLinearEquiv

lemma equiv_comp_koszulComplexAux_zero_eq :
    (exteriorPower.zeroEquiv R M).toLinearMap.comp (koszulComplexAux φ 0) =
      φ.comp (exteriorPower.oneEquiv R M).toLinearMap := by
  ext m
  simp [koszulComplexAux, koszulComplexAuxAlternating_apply]

lemma koszulComplexAux_zero_range_map :
    (koszulComplexAux φ 0).range.map (exteriorPower.zeroEquiv R _).toLinearMap = φ.range := by
  rw [← LinearMap.range_comp, equiv_comp_koszulComplexAux_zero_eq]
  simp

noncomputable def zeroHomologyOfListLinearEquiv (l : List R) :
    (ofList l).homology 0 ≃ₗ[R] R ⧸ Ideal.ofList l :=
  (zeroHomologyLinearEquivAux _).trans (Submodule.Quotient.equiv _ _ (exteriorPower.zeroEquiv R _)
    (by simp [koszulComplexAux_zero_range_map]))

end H0

section regular

open RingTheory.Sequence

/-
Proof route: proof exactness using vanishing of homology, using the inductivity above,
obtain homology `IsZero` from long exact sequence of homology and sequence being regular.
-/

def ofListIsoOfEqAux {rs' rs : List R} {a : R} (eq : rs = rs' ++ [a]) :
    (Fin rs.length → R) ≃ₗ[R] (Fin rs'.length → R) × R := by

  sorry

lemma ofListIsoOfEqAux_comp {rs' rs : List R} {a : R} (eq : rs = rs' ++ [a]) :
    (appendMap (Fintype.linearCombination R rs'.get) a).comp (ofListIsoOfEqAux eq).toLinearMap =
      Fintype.linearCombination R rs.get := by
  sorry

noncomputable def ofListIsoOfEq {rs' rs : List R} {a : R} (eq : rs = rs' ++ [a]) : ofList rs ≅
    koszulComplex (appendMap (Fintype.linearCombination R rs'.get) a) :=
  isoOfEquiv _ (ofListIsoOfEqAux eq) _ (ofListIsoOfEqAux_comp eq)

lemma exactAt_of_isRegular (rs : List R) (reg : IsRegular R rs)
    (i : ℕ) (ne : i ≠ 0) : (ofList rs).ExactAt i := by
  generalize h : rs.length = n
  induction n generalizing rs i with
  | zero =>
    apply ShortComplex.exact_of_isZero_X₂
    exact ofList_X_isZero_of_length_lt rs i (by simpa [h, ← Nat.ne_zero_iff_zero_lt])
  | succ n ih =>
    have nenil : rs ≠ [] := List.ne_nil_of_length_eq_add_one h
    let rs' := rs.dropLast
    have reg' : IsRegular R rs' :=
      sorry
    let a := rs.getLast nenil
    have areg : IsSMulRegular (R ⧸ Ideal.ofList rs') a :=
      sorry
    have eq : rs = rs' ++ [a] := (List.dropLast_concat_getLast nenil).symm
    apply HomologicalComplex.ExactAt.of_iso _ (ofListIsoOfEq eq).symm
    set φ := Fintype.linearCombination R rs'.get
    have ih' (i : ℕ) (ne : i ≠ 0) : IsZero ((koszulComplex φ).homology i) :=
      ((koszulComplex φ).exactAt_iff_isZero_homology i).mp (ih rs' reg' i ne (by simp [rs', h]))
    rw [HomologicalComplex.exactAt_iff_isZero_homology]
    apply ((shortComplexProd_shortExact φ a).homology_exact₂ i).isZero_X₂
      ((ih' i ne).eq_zero_of_src _)
    rcases Nat.exists_eq_succ_of_ne_zero ne with ⟨j, rfl⟩
    rcases eq_or_ne j 0 with rfl|ne0
    · simp only [Nat.succ_eq_add_one]
      rw [← ((shortComplexProd_shortExact φ a).homology_exact₃ (0 + 1) 0 rfl).mono_g_iff]
      simp only [ModuleCat.mono_iff_injective, shortComplexProd_δ_eq]
      simp only [Nat.reduceAdd, pow_zero, one_mul, ← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
      intro x hx
      apply (upOneHomologyIso φ 0).toLinearEquiv.map_eq_zero_iff.mp
      exact (((zeroHomologyOfListLinearEquiv rs').isSMulRegular_congr a).mpr
        areg).right_eq_zero_of_smul hx
    · exact ((upOneHomologyIso φ j).isZero_iff.mpr (ih' j ne0)).eq_zero_of_tgt _

end regular

end koszulComplex
