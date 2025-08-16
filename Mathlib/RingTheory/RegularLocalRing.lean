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

lemma span_eq_top_iff [IsLocalRing R] (S : Set (maximalIdeal R)) :
    Submodule.span R S = ⊤ ↔ Submodule.span R ((Submodule.subtype (maximalIdeal R)) '' S) =
    maximalIdeal R := by
  rw [← Submodule.map_span]
  refine ⟨fun h ↦ by simp [h], fun h ↦ ?_⟩
  rw [← Submodule.comap_map_eq_of_injective (maximalIdeal R).injective_subtype
    (Submodule.span R S), h, Submodule.comap_subtype_self]

open Set in
lemma spanFinrank_maximalIdeal [IsLocalRing R] [IsNoetherianRing R] :
    (Submodule.spanFinrank (maximalIdeal R)) =
    Module.finrank (ResidueField R) (CotangentSpace R) := by
  let fg : Module.Finite (ResidueField R) (CotangentSpace R) := inferInstance
  let fg' : (maximalIdeal R).FG := (isNoetherianRing_iff_ideal_fg R).mp inferInstance _
  have : Submodule.spanFinrank (⊤ : Submodule (ResidueField R) (CotangentSpace R)) =
    Module.rank (ResidueField R) (CotangentSpace R) := by
    rw [← Submodule.fg_iff_spanRank_eq_spanFinrank.mpr fg.1, Submodule.rank_eq_spanRank_of_free]
  simp only [← Module.finrank_eq_rank, Nat.cast_inj] at this
  rw [← this]
  apply le_antisymm
  · have span : Submodule.span R
      ((⊤ : Submodule (ResidueField R) (CotangentSpace R)).generators.image Quotient.out) = ⊤ := by
      apply IsLocalRing.CotangentSpace.span_image_eq_top_iff.mp
      convert Submodule.span_generators (⊤ : Submodule (ResidueField R) (CotangentSpace R))
      have : ⇑(maximalIdeal R).toCotangent ∘ Quotient.out = id := by
        ext
        exact Submodule.Quotient.mk_out _
      rw [← Set.image_comp, this, image_id]
    rw [span_eq_top_iff, ← Set.image_comp] at span
    rw [← Submodule.FG.generators_ncard fg.1, ← congrArg Submodule.spanFinrank span]
    apply le_trans (Submodule.spanFinrank_span_le_ncard_of_finite
      (Finite.image _ fg.1.finite_generators)) (Set.ncard_image_le fg.1.finite_generators)
  · let G := ({x | ↑x ∈ (maximalIdeal R).generators} : Set (maximalIdeal R))
    have : Submodule.span R G = ⊤ := by
      simp only [span_eq_top_iff, Submodule.subtype_apply, Ideal.submodule_span_eq, G]
      convert (maximalIdeal R).span_generators
      ext
      simpa using fun a ↦ Submodule.FG.generators_mem (maximalIdeal R) a
    have fin : G.Finite := Set.Finite.of_injOn (by simp [MapsTo, G]) injOn_subtype_val
        (Submodule.FG.finite_generators fg')
    rw [← IsLocalRing.CotangentSpace.span_image_eq_top_iff.mpr this,
      ← Submodule.FG.generators_ncard fg']
    apply le_trans (Submodule.spanFinrank_span_le_ncard_of_finite (Finite.image _ fin))
    exact le_trans (Set.ncard_image_le fin) (Set.ncard_le_ncard_of_injOn Subtype.val (by simp [G])
      injOn_subtype_val (Submodule.FG.finite_generators fg'))

lemma quotient_isRegularLocalRing_tfae [IsRegularLocalRing R] (S : Finset R)
    (sub : (S : Set R) ⊆ maximalIdeal R) :
    [∃ (T : Finset R), S ⊆ T ∧ T.card = ringKrullDim R ∧ Ideal.span T = maximalIdeal R,
     LinearIndependent (ResidueField R) ((⇑(maximalIdeal R).toCotangent).comp (Set.inclusion sub)),
     IsRegularLocalRing (R ⧸ Ideal.span (S : Set R)) ∧
     (ringKrullDim (R ⧸ Ideal.span (S : Set R)) + S.card = ringKrullDim R)].TFAE := by
  tfae_have 1 → 2 := by
    rintro ⟨T, h, card, span⟩
    have Tsub : (T : Set R) ⊆ maximalIdeal R := by simpa [← span] using Ideal.subset_span
    have : LinearIndependent (ResidueField R)
      ((⇑(maximalIdeal R).toCotangent).comp (Set.inclusion Tsub)) := by
      apply linearIndependent_of_top_le_span_of_card_eq_finrank
      · simp only [Finset.coe_sort_coe, Set.range_comp, Set.range_inclusion Tsub,
          SetLike.coe_sort_coe, Finset.mem_coe, top_le_iff,
          IsLocalRing.CotangentSpace.span_image_eq_top_iff]
        simp only [span_eq_top_iff, Submodule.subtype_apply, Ideal.submodule_span_eq]
        convert span
        ext
        simpa using fun a ↦ Tsub a
      · rw [← spanFinrank_maximalIdeal R, ← Nat.cast_inj (R := WithBot ℕ∞),
          (isRegularLocalRing_iff R).mp ‹_›, ← card]
        simp
    have li := LinearIndependent.comp this (Set.inclusion h) (Set.inclusion_injective h)
    have inc : Set.inclusion Tsub ∘ Set.inclusion h = Set.inclusion sub := rfl
    simpa [← Function.comp_assoc, ← inc] using li
  tfae_have 2 → 3 := by
    intro li

    sorry
  tfae_have 3 → 1 := by
    rintro ⟨reg, dim⟩

    sorry
  tfae_finish

theorem isDomain_of_isRegularLocalRing [IsRegularLocalRing R] : IsDomain R := by
  sorry

open RingTheory.Sequence in
theorem isRegular_of_span_eq_maximalIdeal [IsRegularLocalRing R] (rs : List R)
    (eq : Ideal.ofList rs = maximalIdeal R) (len : rs.length = ringKrullDim R) :
    IsRegular R rs := by
  sorry

end
