/-
Copyright (c) 2025 Jingting Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jingting Wang
-/
module

public import Mathlib.Algebra.Polynomial.FieldDivision
public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
public import Mathlib.RingTheory.KrullDimension.NonZeroDivisors
public import Mathlib.RingTheory.KrullDimension.PID
public import Mathlib.RingTheory.LocalRing.ResidueField.Fiber

/-!
# Krull dimension of polynomial ring

This file proves properties of the krull dimension of the polynomial ring over a commutative ring

## Main results

* `Polynomial.ringKrullDim_le`: the krull dimension of the polynomial ring over a commutative ring
  `R` is less than `2 * (ringKrullDim R) + 1`.
-/

@[expose] public section

open Polynomial

theorem Polynomial.ringKrullDim_le {R : Type*} [CommRing R] :
    ringKrullDim R[X] ≤ 2 * (ringKrullDim R) + 1 := by
  rw [ringKrullDim, ringKrullDim]
  apply Order.krullDim_le_of_krullDim_preimage_le' C.specComap ?_ (fun p ↦ ?_)
  · exact fun {a b} h ↦ Ideal.comap_mono h
  · rw [← Polynomial.algebraMap_eq, Order.krullDim_eq_of_orderIso
      (PrimeSpectrum.preimageOrderIsoTensorResidueField R (Polynomial R) p), ← ringKrullDim,
      ← ringKrullDim_eq_of_ringEquiv (polyEquivTensor R (p.asIdeal.ResidueField)).toRingEquiv,
      ← Ring.krullDimLE_iff]
    infer_instance

variable (R : Type*) [CommRing R]

open IsLocalRing

lemma eq_radical_of_maximalIdeal_mem_minimalPrimes [IsLocalRing R] (I : Ideal R)
    (mem : maximalIdeal R ∈ I.minimalPrimes) : maximalIdeal R = I.radical := by
  have eq : I.minimalPrimes = {maximalIdeal R} := by
    ext p
    refine ⟨fun h ↦ Set.mem_singleton_iff.mpr ?_, fun h ↦ by simpa [Set.mem_singleton_iff.mp h]⟩
    let _ : p.IsPrime := h.1.1
    exact Minimal.eq_of_le mem.out h.1 (le_maximalIdeal_of_isPrime p)
  simpa [eq] using Ideal.sInf_minimalPrimes (I := I)

namespace Polynomial

variable [IsNoetherianRing R]

lemma height_map_maximalIdeal [IsLocalRing R] :
    ((maximalIdeal R).map C).height = (maximalIdeal R).height := by
  let : (Ideal.map C (maximalIdeal R)).IsPrime := Ideal.isPrime_map_C_of_isPrime
    (Ideal.IsMaximal.isPrime' (maximalIdeal R))
  apply le_antisymm
  · rcases (maximalIdeal R).exists_finset_card_eq_height_of_isNoetherianRing with ⟨s, min, card⟩
    have eq := eq_radical_of_maximalIdeal_mem_minimalPrimes R _ min
    have eqrad : Ideal.map C (maximalIdeal R) = ((Ideal.span s).map C).radical := by
      apply le_antisymm _ ((Ideal.IsPrime.radical_le_iff ‹_›).mpr (Ideal.map_mono min.1.2))
      simpa [eq_radical_of_maximalIdeal_mem_minimalPrimes R _ min] using Ideal.map_radical_le _
    let _ : ((Ideal.span (s : Set R)).map C).radical.IsPrime := by simpa [← eqrad]
    have : Ideal.map C (maximalIdeal R) ∈ ((Ideal.span s).map C).minimalPrimes := by
      rw [eqrad]
      refine ⟨?_, fun p ⟨prime, Ile⟩ _ ↦ (Ideal.IsPrime.radical_le_iff prime).mpr Ile⟩
      simpa [Ideal.radical_le_radical_iff.mp (le_refl _)]
    apply le_trans (Ideal.height_le_spanRank_toENat_of_mem_minimal_primes _ _ this)
    have fg : (Ideal.map C (Ideal.span (s : Set R))).FG :=
      (isNoetherianRing_iff_ideal_fg R[X]).mp inferInstance _
    simp only [Submodule.fg_iff_spanRank_eq_spanFinrank.mpr fg, map_natCast, ← card, Nat.cast_le]
    rw [Ideal.map_span, ← Set.ncard_coe_finset s]
    apply le_trans (Submodule.spanFinrank_span_le_ncard_of_finite (Set.toFinite _))
      (Set.ncard_image_le s.finite_toSet)
  · simp only [Ideal.height_eq_primeHeight, Ideal.primeHeight]
    let map' : PrimeSpectrum R → PrimeSpectrum R[X] := fun p ↦
      ⟨p.1.map C, Ideal.isPrime_map_C_of_isPrime p.2⟩
    apply Order.height_le_height_apply_of_strictMono map'
    intro p q lt
    simp only [← PrimeSpectrum.asIdeal_lt_asIdeal, map']
    apply (Set.ssubset_iff_of_subset (Ideal.map_mono (le_of_lt lt))).mpr
    rcases (Set.ssubset_iff_of_subset (le_of_lt lt)).mp lt with ⟨x, hx⟩
    use C x
    simp only [SetLike.mem_coe, Ideal.mem_map_of_mem _ hx.1, Ideal.mem_map_C_iff, not_forall,
      true_and]
    use 0
    simpa using hx.2

lemma height_of_comap_eq_maximalIdeal [IsLocalRing R] (m : Ideal R[X]) [h : m.IsPrime]
    (eqm : m.comap C = maximalIdeal R) : m.height ≤ (maximalIdeal R).height + 1 := by
  let : (Ideal.map C (maximalIdeal R)).IsPrime := Ideal.isPrime_map_C_of_isPrime
    (Ideal.IsMaximal.isPrime' (maximalIdeal R))
  have maple : (maximalIdeal R).map C ≤ m := by simp [Ideal.map_le_iff_le_comap, eqm]
  let _ : IsPrincipalIdealRing (IsLocalRing.ResidueField R)[X] := inferInstance
  rcases IsPrincipalIdealRing.principal (Ideal.map (mapRingHom (residue R)) m) with ⟨x, hx⟩
  rcases map_surjective (residue R) residue_surjective x with ⟨y, hy⟩
  have eqsup : m = (maximalIdeal R).map C ⊔ Ideal.span {y} := by
    calc
      m = m ⊔ RingHom.ker (mapRingHom (residue R)) := by
        simpa only [ker_mapRingHom, left_eq_sup, ker_residue] using maple
      _ = ((Ideal.span {y}).map (mapRingHom (residue R))).comap (mapRingHom (residue R)) := by
        simp [← Ideal.comap_map_of_surjective' (mapRingHom (residue R))
          (map_surjective (residue R) residue_surjective), hx, Ideal.map_span, hy]
      _ = _ := by
        simp only [Ideal.comap_map_of_surjective' (mapRingHom (residue R))
          (map_surjective (residue R) residue_surjective), sup_comm, ker_mapRingHom, ker_residue]
  rcases (maximalIdeal R).exists_finset_card_eq_height_of_isNoetherianRing with ⟨s, min, card⟩
  have eq := eq_radical_of_maximalIdeal_mem_minimalPrimes R _ min
  have eqrad : Ideal.map C (maximalIdeal R) = ((Ideal.span s).map C).radical := by
    apply le_antisymm _ ((Ideal.IsPrime.radical_le_iff ‹_›).mpr (Ideal.map_mono min.1.2))
    simpa [eq_radical_of_maximalIdeal_mem_minimalPrimes R _ min] using Ideal.map_radical_le _
  have : m ∈ (((Ideal.span s).map C) ⊔ Ideal.span {y}).minimalPrimes := by
    refine ⟨?_, fun p ⟨prime, le⟩ _ ↦ by
      simpa [eqsup, eqrad, Ideal.IsPrime.radical_le_iff prime] using le⟩
    simp only [h, sup_le_iff, true_and]
    simpa only [eqsup, le_sup_right, and_true] using le_sup_of_le_left (Ideal.map_mono min.1.2)
  rw [Ideal.map_span, ← Ideal.span_union] at this
  apply le_trans (Ideal.height_le_spanRank_toENat_of_mem_minimal_primes _ _ this)
  have fg : (Ideal.span (⇑C '' ↑s ∪ {y})).FG :=
    (isNoetherianRing_iff_ideal_fg R[X]).mp inferInstance _
  simp only [Submodule.fg_iff_spanRank_eq_spanFinrank.mpr fg, map_natCast, ← card]
  rw [← ENat.coe_one, ← ENat.coe_add, ENat.coe_le_coe, ← Set.ncard_coe_finset s]
  apply le_trans (Submodule.spanFinrank_span_le_ncard_of_finite (Set.toFinite _))
  apply le_trans (Set.ncard_union_le _ _)
  simpa only [Set.ncard_singleton, add_le_add_iff_right] using (Set.ncard_image_le s.finite_toSet)

open Ideal in
lemma height_le_height_comap_succ (p : Ideal R[X]) [p.IsPrime] :
    p.height ≤ (p.comap C).height + 1 := by
  let q := p.comap C
  let S := (Localization.AtPrime q)[X]
  let pc := Submonoid.map Polynomial.C.toMonoidHom q.primeCompl
  let _ : Algebra R[X] S := algebra R (Localization.AtPrime q)
  have _ : IsLocalization pc S := {
    map_units x := by
      rcases x.2 with ⟨y, mem, eq⟩
      apply IsUnit.of_mul_eq_one (C (Localization.mk 1 ⟨y, mem⟩))
      simp [← eq, S, ← map_mul, ← Localization.mk_one_eq_algebraMap, Localization.mk_mul]
    surj z := by
      induction z using Polynomial.induction_on'
      · rename_i f g hf hg
        rcases hf with ⟨⟨x1, y1⟩, h1⟩
        rcases hg with ⟨⟨x2, y2⟩, h2⟩
        use (x2 * y1.1 + x1 * y2.1, y1 * y2)
        simp only [Submonoid.coe_mul, map_mul, add_mul, map_add]
        nth_rw 4 [mul_comm]
        simp [← mul_assoc, h1, h2, add_comm]
      · rename_i n a
        rcases Localization.mkHom_surjective a with ⟨⟨x, y⟩, h⟩
        have : y.1 ∉ q := y.2
        use ((monomial n) x, ⟨C y.1, by simpa [pc]⟩)
        simp only [← h, Localization.mkHom_apply, algebraMap_def, coe_mapRingHom, map_C, ←
          Localization.mk_one_eq_algebraMap, monomial_mul_C, map_monomial, S, Localization.mk_mul]
        congr 1
        apply Localization.mk_eq_mk_iff.mpr (Localization.r_of_eq ?_)
        simp [mul_comm]
    exists_of_eq {x y} eq := by
      have eq' (n : ℕ) : (algebraMap R (Localization.AtPrime q)) (Polynomial.coeff x n) =
        (algebraMap R (Localization.AtPrime q)) (Polynomial.coeff y n) := by
        simp only [algebraMap_def, coe_mapRingHom, S] at eq
        have : coeff (map (algebraMap R (Localization.AtPrime q)) x) n =
          coeff (map (algebraMap R (Localization.AtPrime q)) y) n := by rw [eq]
        simpa
      let g : ℕ → q.primeCompl := fun n ↦ Classical.choose (IsLocalization.exists_of_eq (eq' n))
      have g_spec (n : ℕ) := Classical.choose_spec
        (IsLocalization.exists_of_eq (M := q.primeCompl) (eq' n))
      let s := ∏ n ∈ x.1.1 ∪ y.1.1, g n
      have : s.1 ∉ q := s.2
      use ⟨C s.1, by simpa [pc]⟩
      ext n
      simp only [coeff_C_mul, s]
      by_cases mem : n ∈ x.1.1 ∪ y.1.1
      · rcases Finset.dvd_prod_of_mem g mem with ⟨t, ht⟩
        simp only [ht, Submonoid.coe_mul, mul_comm _ t.1, mul_assoc]
        rw [g_spec n]
      · simp only [Finset.mem_union, Finsupp.mem_support_iff, ne_eq, not_or, not_not] at mem
        simp [← Polynomial.toFinsupp_apply, mem] }
  let pS := p.map (algebraMap R[X] S)
  have disj : Disjoint (pc : Set R[X]) (p : Set R[X]) := by
    simpa [pc, q] using Set.disjoint_image_left.mpr
      (Set.disjoint_compl_left_iff_subset.mpr (fun _ a ↦ a))
  have : pS.IsPrime :=  IsLocalization.isPrime_of_isPrime_disjoint pc _ _ ‹_› disj
  have : pS.comap C = maximalIdeal (Localization.AtPrime q) := by
    rw [← IsLocalization.map_comap q.primeCompl _ (pS.comap C),
      ← IsLocalization.map_comap q.primeCompl _ (maximalIdeal (Localization.AtPrime q))]
    simp only [comap_comap, S, pS]
    rw [← Polynomial.algebraMap_eq (R := Localization.AtPrime q),
      ← IsScalarTower.algebraMap_eq R (Localization.AtPrime q) (Localization.AtPrime q)[X],
      IsScalarTower.algebraMap_eq R R[X] (Localization.AtPrime q)[X], ← comap_comap,
      IsLocalization.comap_map_of_isPrime_disjoint pc _ _ ‹_› disj,
      IsLocalization.AtPrime.comap_maximalIdeal (Localization.AtPrime q) q]
    rfl
  have le := height_of_comap_eq_maximalIdeal (Localization.AtPrime q) _ this
  nth_rw 1 [← IsLocalization.comap_map_of_isPrime_disjoint pc S p ‹_› disj,
    IsLocalization.height_comap pc pS]
  apply le_trans (height_of_comap_eq_maximalIdeal (Localization.AtPrime q) _ this)
  rw [← IsLocalization.height_comap q.primeCompl, Localization.AtPrime.comap_maximalIdeal]

/-- If `R` is Noetherian, `dim R[X] = dim R + 1`. -/
lemma ringKrullDim_of_isNoetherianRing : ringKrullDim R[X] = ringKrullDim R + 1 := by
  apply le_antisymm _ ringKrullDim_succ_le_ringKrullDim_polynomial
  by_cases ntr : Nontrivial R
  · have un : ringKrullDim R ≠ ⊥ := ne_bot_of_le_ne_bot WithBot.zero_ne_bot
      ringKrullDim_nonneg_of_nontrivial
    rw [← Ideal.sup_primeHeight_eq_ringKrullDim, ← WithBot.coe_unbot _ un, ← WithBot.coe_one,
      ← WithBot.coe_add, WithBot.coe_le_coe]
    simp only [iSup_le_iff, ← Ideal.height_eq_primeHeight]
    intro p hp
    apply le_trans (height_le_height_comap_succ R p) (WithBot.coe_le_coe.mp _)
    let _ : (Ideal.comap C p).IsPrime := Ideal.comap_isPrime C p
    simpa [Ideal.height_eq_primeHeight] using
      add_le_add_left Ideal.primeHeight_le_ringKrullDim 1
  · have : Subsingleton R := not_nontrivial_iff_subsingleton.mp ntr
    have : Subsingleton R[X] := subsingleton_iff_subsingleton.mpr this
    simp [ringKrullDim_eq_bot_of_subsingleton]

end Polynomial

/-- If `R` is Noetherian, `dim R[X] = dim R + 1`. -/
lemma MvPolynomial.ringKrullDim_of_isNoetherianRing [IsNoetherianRing R] (n : ℕ) :
  ringKrullDim (MvPolynomial (Fin n) R) = ringKrullDim R + n := by
  induction n
  · simp [ringKrullDim_eq_of_ringEquiv (isEmptyRingEquiv R (Fin 0))]
  · rename_i n ih
    rw [ringKrullDim_eq_of_ringEquiv (MvPolynomial.finSuccEquiv R n).toRingEquiv,
      Polynomial.ringKrullDim_of_isNoetherianRing (MvPolynomial (Fin n) R), ih,
      Nat.cast_add, Nat.cast_one, ← add_assoc]
