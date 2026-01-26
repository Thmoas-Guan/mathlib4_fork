/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.Regular.RegularSequence
public import Mathlib.RingTheory.CohenMacaulay.Catenary
public import Mathlib.RingTheory.CohenMacaulay.Maximal
public import Mathlib.RingTheory.KoszulComplex.Defs

/-!

# Define Complete Intersection Ring

-/

@[expose] public section

open IsLocalRing RingTheory.Sequence

universe u

variable (R : Type u) [CommRing R]

section preliminaries

variable [IsNoetherianRing R] [IsLocalRing R]

instance : IsNoetherianRing (AdicCompletion (maximalIdeal R) R) := sorry

instance : IsLocalRing (AdicCompletion (maximalIdeal R) R) := sorry

instance : IsAdicComplete (maximalIdeal (AdicCompletion (maximalIdeal R) R))
    (AdicCompletion (maximalIdeal R) R) := sorry

lemma ringKrullDim_adicCompletion_eq :
    ringKrullDim (AdicCompletion (maximalIdeal R) R) = ringKrullDim R := by
  --!!!
  sorry

lemma spanFinrank_maximalIdeal_adicCompletion_eq :
    (maximalIdeal (AdicCompletion (maximalIdeal R) R)).spanFinrank =
    (maximalIdeal R).spanFinrank := by
  --!!!
  sorry

end preliminaries
