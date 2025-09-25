/-
Copyright (c) 2025 Jingting Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jingting Wang
-/
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.RingTheory.KrullDimension.PID
import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem

/-!
# Krull dimension of polynomial ring

This file proves properties of the krull dimension of the polynomial ring over a commutative ring

## Main results

* `Polynomial.ringKrullDim_le`: the krull dimension of the polynomial ring over a commutative ring
  `R` is less than `2 * (ringKrullDim R) + 1`.
-/

open Polynomial

theorem Polynomial.ringKrullDim_le {R : Type*} [CommRing R] :
    ringKrullDim R[X] ≤ 2 * (ringKrullDim R) + 1 := by
  rw [ringKrullDim, ringKrullDim]
  apply Order.krullDim_le_of_krullDim_preimage_le' C.specComap ?_ (fun p ↦ ?_)
  · exact fun {a b} h ↦ Ideal.comap_mono h
  · rw [show C = (algebraMap R (Polynomial R)) from rfl, Order.krullDim_eq_of_orderIso
      (PrimeSpectrum.preimageOrderIsoTensorResidueField R (Polynomial R) p), ← ringKrullDim,
      ← ringKrullDim_eq_of_ringEquiv (polyEquivTensor R (p.asIdeal.ResidueField)).toRingEquiv,
      ← Ring.krullDimLE_iff]
    infer_instance

variable (R : Type*) [CommRing R]

lemma comap_eq_maximalIdeal_of_IsMaximal (m : Ideal R[X]) [m.IsMaximal] :
    (m.comap C).IsMaximal := by
  --Polynomial.constantCoeff
  sorry

variable [IsLocalRing R]

open IsLocalRing

lemma eq_radical_of_maximalIdeal_mem_minimalPrimes (I : Ideal R)
    (mem : maximalIdeal R ∈ I.minimalPrimes) : maximalIdeal R = I.radical := by
  have eq : I.minimalPrimes = {maximalIdeal R} := by
    ext p
    refine ⟨fun h ↦ Set.mem_singleton_iff.mpr ?_, fun h ↦ by simpa [Set.mem_singleton_iff.mp h]⟩
    let _ : p.IsPrime := h.1.1
    exact Minimal.eq_of_le mem.out h.1 (le_maximalIdeal_of_isPrime p)
  simpa [eq] using Ideal.sInf_minimalPrimes (I := I)

namespace Polynomial

variable [IsNoetherianRing R]

lemma height_map_maximalIdeal : ((maximalIdeal R).map C).height = (maximalIdeal R).height := by
  let : (Ideal.map C (maximalIdeal R)).IsPrime := Ideal.isPrime_map_C_of_isPrime
    (Ideal.IsMaximal.isPrime' (maximalIdeal R))
  apply le_antisymm
  · rcases (maximalIdeal R).exists_finset_card_eq_height_of_isNoetherianRing with ⟨s, min, card⟩
    have eq := eq_radical_of_maximalIdeal_mem_minimalPrimes R _ min
    have eqrad : Ideal.map C (maximalIdeal R) = ((Ideal.span s).map C).radical := by
      apply le_antisymm _ ((Ideal.IsPrime.radical_le_iff ‹_›).mpr (Ideal.map_mono min.1.2))
      simpa [eq_radical_of_maximalIdeal_mem_minimalPrimes R _ min] using Ideal.map_radical_le _
    let _ : ((Ideal.span s.toSet).map C).radical.IsPrime := by simpa [← eqrad]
    have : Ideal.map C (maximalIdeal R) ∈ ((Ideal.span s).map C).minimalPrimes := by
      rw [eqrad]
      refine ⟨?_, fun p ⟨prime, Ile⟩ _ ↦ (Ideal.IsPrime.radical_le_iff prime).mpr Ile⟩
      simpa [Ideal.radical_le_radical_iff.mp (le_refl _)]
    apply le_trans (Ideal.height_le_spanRank_toENat_of_mem_minimal_primes _ _ this)
    have fg : (Ideal.map C (Ideal.span s.toSet)).FG :=
      (isNoetherianRing_iff_ideal_fg R[X]).mp inferInstance _
    simp only [Submodule.fg_iff_spanRank_eq_spanFinrank.mpr fg, map_natCast, ← card, Nat.cast_le]
    rw [Ideal.map_span, ← Set.ncard_coe_finset s]
    apply le_trans (Submodule.spanFinrank_span_le_ncard_of_finite
      (Set.Finite.image _ s.finite_toSet)) (Set.ncard_image_le s.finite_toSet)
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

lemma height_maximal (m : Ideal R[X]) [m.IsMaximal] : m.height = (maximalIdeal R).height + 1 := by
  let : (Ideal.map C (maximalIdeal R)).IsPrime := Ideal.isPrime_map_C_of_isPrime
    (Ideal.IsMaximal.isPrime' (maximalIdeal R))
  have eqm : m.comap C = maximalIdeal R := eq_maximalIdeal (comap_eq_maximalIdeal_of_IsMaximal R m)
  apply le_antisymm
  · let _ : IsPrincipalIdealRing (IsLocalRing.ResidueField R)[X] := inferInstance
    rcases IsPrincipalIdealRing.principal (Ideal.map (mapRingHom (residue R)) m) with ⟨x, hx⟩
    rcases map_surjective (residue R) residue_surjective x with ⟨y, hy⟩
    have eqsup : m = (maximalIdeal R).map C ⊔ Ideal.span {y} := by

      sorry
    rcases (maximalIdeal R).exists_finset_card_eq_height_of_isNoetherianRing with ⟨s, min, card⟩
    have eq := eq_radical_of_maximalIdeal_mem_minimalPrimes R _ min
    have eqrad : Ideal.map C (maximalIdeal R) = ((Ideal.span s).map C).radical := by
      apply le_antisymm _ ((Ideal.IsPrime.radical_le_iff ‹_›).mpr (Ideal.map_mono min.1.2))
      simpa [eq_radical_of_maximalIdeal_mem_minimalPrimes R _ min] using Ideal.map_radical_le _
    have : m ∈ (((Ideal.span s).map C) ⊔ Ideal.span {y}).minimalPrimes := by
      refine ⟨?_, fun p ⟨prime, le⟩ _ ↦ by
        simpa [eqsup, eqrad, Ideal.IsPrime.radical_le_iff prime] using le⟩
      simp only [Ideal.IsMaximal.isPrime' m, sup_le_iff, true_and]
      simp only [eqsup, le_sup_right, and_true]
      exact le_sup_of_le_left (Ideal.map_mono min.1.2)

    sorry
  · rw [← height_map_maximalIdeal, Ideal.height_eq_primeHeight, Ideal.height_eq_primeHeight]
    apply Ideal.primeHeight_add_one_le_of_lt

    sorry

theorem ringKrullDim_of_isNoetherianRing_of_isLocalRing :
    ringKrullDim R[X] = ringKrullDim R + 1 := by
  sorry

end Polynomial
