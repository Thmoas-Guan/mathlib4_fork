/-
Copyright (c) 2025 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
import Mathlib.RingTheory.Ideal.Cotangent
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.RingTheory.Regular.RegularSequence
/-!
# Define Regular Local Ring
-/

open IsLocalRing

variable (R : Type*) [CommRing R]

class IsRegularLocalRing : Prop extends IsLocalRing R, IsNoetherianRing R where
  reg : (Submodule.spanFinrank (maximalIdeal R)) = ringKrullDim R

lemma isRegularLocalRing_iff [IsLocalRing R] [IsNoetherianRing R] :
    IsRegularLocalRing R ↔ (Submodule.spanFinrank (maximalIdeal R)) = ringKrullDim R :=
  ⟨fun ⟨h⟩ ↦ h, fun h ↦ ⟨h⟩⟩

lemma ringKrullDim_le_spanFinrank_maximalIdeal [IsLocalRing R] [IsNoetherianRing R] :
    ringKrullDim R ≤ (Submodule.spanFinrank (maximalIdeal R)) :=
  le_of_eq_of_le IsLocalRing.maximalIdeal_height_eq_ringKrullDim.symm
    (WithBot.coe_le_coe.mpr (Ideal.height_le_spanFinrank (maximalIdeal R) Ideal.IsPrime.ne_top'))

lemma isRegularLocalRing_of_exist_span [IsLocalRing R] [IsNoetherianRing R] (S : Finset R)
    (span : Ideal.span S = maximalIdeal R) (card : S.card ≤ ringKrullDim R) :
    IsRegularLocalRing R := by
  apply (isRegularLocalRing_iff _).mpr (le_antisymm _ (ringKrullDim_le_spanFinrank_maximalIdeal R))
  apply le_trans _ card
  rw [← span, ← Ideal.submodule_span_eq, ← Set.ncard_coe_finset S, Nat.cast_le]
  exact Submodule.spanFinrank_span_le_ncard_of_finite S.finite_toSet

variable {R} in
lemma IsLocalRing.comap_maximalIdeal [IsLocalRing R] {R' : Type*} [CommRing R'] [IsLocalRing R']
    (e : R ≃+* R') : maximalIdeal R = Ideal.comap e (maximalIdeal R') := by
  ext
  simp

variable {R} in
lemma IsLocalRing.map_maximalIdeal [IsLocalRing R] {R' : Type*} [CommRing R'] [IsLocalRing R']
    (e : R ≃+* R') : Ideal.map e (maximalIdeal R) = maximalIdeal R' := by
  rw [← Ideal.map_comap_of_surjective _ e.surjective (maximalIdeal R'),
    IsLocalRing.comap_maximalIdeal e]

variable {R} in
lemma isRegularLocalRing_of_ringEquiv [IsRegularLocalRing R] {R' : Type*} [CommRing R']
    (e : R ≃+* R') : IsRegularLocalRing R' := by
  let _ := e.isLocalRing
  let _ := isNoetherianRing_of_ringEquiv R e
  have fg : (maximalIdeal R).FG := (isNoetherianRing_iff_ideal_fg R).mp inferInstance _
  let _ : Fintype (Submodule.generators (maximalIdeal R)) :=
    (Submodule.FG.finite_generators fg).fintype
  apply isRegularLocalRing_of_exist_span R' ((maximalIdeal R).generators.toFinset.map e.toEmbedding)
  · simp only [RingEquiv.toEquiv_eq_coe, Finset.coe_map, Equiv.coe_toEmbedding, EquivLike.coe_coe,
      Set.coe_toFinset, ← Ideal.map_span]
    rw [← Ideal.submodule_span_eq, Submodule.span_generators (maximalIdeal R)]
    exact IsLocalRing.map_maximalIdeal e
  · simpa [← ringKrullDim_eq_of_ringEquiv e, ← IsRegularLocalRing.reg,
      ← Submodule.FG.generators_ncard fg] using le_of_eq (Set.ncard_eq_toFinset_card' _).symm

section

variable [IsLocalRing R]

lemma spanFinrank_eq_finrank_quotient (M : Type*) [AddCommGroup M] [Module R M]
    [Module.Finite R M] : (⊤ : Submodule R M).spanFinrank =
    Module.finrank (R ⧸ (maximalIdeal R)) (M ⧸ (maximalIdeal R) • (⊤ : Submodule R M)) := by
  sorry

lemma spanFinrank_maximalIdeal (fg : (maximalIdeal R).FG) :
    (Submodule.spanFinrank (maximalIdeal R)) =
    Module.finrank (ResidueField R) (CotangentSpace R) := by
  sorry

lemma quotient_isRegularLocalRing_tfae (S : Finset R) (sub : (S : Set R) ⊆ maximalIdeal R)
    [IsRegularLocalRing R] :
    [∃ (T : Finset R), S ⊆ T ∧ T.card = ringKrullDim R ∧ Ideal.span T = maximalIdeal R,
     LinearIndependent (ResidueField R) ((⇑(maximalIdeal R).toCotangent).comp (Set.inclusion sub)),
     IsRegularLocalRing (R ⧸ Ideal.span (S : Set R)) ∧
     (ringKrullDim (R ⧸ Ideal.span (S : Set R)) + S.card = ringKrullDim R),
     IsRegularLocalRing (R ⧸ Ideal.span (S : Set R))].TFAE := by
  sorry

theorem isDomain_of_isRegularLocalRing [IsRegularLocalRing R] : IsDomain R := by
  sorry

open RingTheory.Sequence in
theorem isRegular_of_span_eq_maximalIdeal (rs : List R) (eq : Ideal.ofList rs = maximalIdeal R)
    (len : rs.length = ringKrullDim R) : IsRegular R rs := by
  sorry

end
