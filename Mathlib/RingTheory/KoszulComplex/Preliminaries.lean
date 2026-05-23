/-
Copyright (c) 2026 Jingting Wang, Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jingting Wang, Nailin Guan
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.LinearAlgebra.ExteriorPower.Basis

/-!
# Preliminaries
-/

public section

universe u v

variable {R : Type u} [CommRing R]

namespace ModuleCat

@[simp]
lemma ofHom_zero {M N : Type v} [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] : ModuleCat.ofHom (0 : M →ₗ[R] N) = 0 := rfl

@[simp]
lemma ofHom_add {M N : Type v} [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (f g : M →ₗ[R] N) :
    ModuleCat.ofHom (f + g) = ModuleCat.ofHom f + ModuleCat.ofHom g := rfl

end ModuleCat

namespace exteriorPower

variable {n : ℕ} {M N : Type*} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

theorem subtype_comp_map_eq (f : M →ₗ[R] N) :
    (Submodule.subtype _) ∘ₗ (map n f) =
    (ExteriorAlgebra.map f).toLinearMap ∘ₗ (Submodule.subtype _) :=
  linearMap_ext <| AlternatingMap.ext fun m ↦ (by simp)

@[simp]
theorem coe_map (f : M →ₗ[R] N) (x : ⋀[R]^n M) : map n f x = ExteriorAlgebra.map f x.1 :=
  congr($(subtype_comp_map_eq f) x)

end exteriorPower

section

variable (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M]

namespace exteriorPower

lemma span_ιMulti_orderEmbedding_of_span_eq_top' {ι : Type*} [LinearOrder ι] {g : ι → M}
    (hg : Submodule.span R (Set.range g) = ⊤) (n : ℕ) :
    Submodule.span R (Set.range (fun (x : Fin n ↪o ι) ↦ ιMulti R _ (g ∘ x))) = ⊤ := by
  -- Route correction: reuse mathlib's spanning theorem and only reindex the family.
  have hspan := ιMulti_family_span_of_span (R := R) (n := n) hg
  have hrange : Set.range (ιMulti_family R n g) =
      Set.range (fun x : Fin n ↪o ι ↦ ιMulti R n (g ∘ x)) := by
    ext y
    constructor
    · rintro ⟨s, rfl⟩
      exact ⟨Set.powersetCard.ofFinEmbEquiv.symm s, by simp [ιMulti_family]⟩
    · rintro ⟨x, rfl⟩
      exact ⟨Set.powersetCard.ofFinEmbEquiv x, by simp [ιMulti_family]⟩
  simpa [hrange] using hspan

end exteriorPower

lemma subsingleton_of_card_generators_le {ι : Type*} [Finite ι] [LinearOrder ι] (g : ι → M)
    (hg : Submodule.span R (Set.range g) = ⊤) (i : ℕ) (hi : Nat.card ι < i) :
    Subsingleton (⋀[R]^i M) := by
  letI : Fintype ι := Fintype.ofFinite ι
  have hcard : Fintype.card ι < i := by simpa [Nat.card_eq_fintype_card] using hi
  have hbotTop : (⊥ : Submodule R (⋀[R]^i M)) = ⊤ := by
    rw [← exteriorPower.span_ιMulti_orderEmbedding_of_span_eq_top' (R := R) (M := M) hg i]
    convert Submodule.span_empty.symm
    refine Set.range_eq_empty_iff.mpr ⟨fun f ↦ ?_⟩
    absurd hcard
    simpa using Fintype.card_le_of_injective f f.injective
  exact (Submodule.subsingleton_iff R).mp <| (subsingleton_iff_bot_eq_top).mp hbotTop

end
