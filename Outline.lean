module

public import Mathlib

section DerivedFunctor

--classical construction of derived functor

#check CategoryTheory.injectiveResolutions

#check CategoryTheory.Functor.rightDerivedToHomotopyCategory

#check CategoryTheory.Functor.rightDerived

--the related problems

#check CategoryTheory.Tor
#check CategoryTheory.Tor'

--we are not able to unify the two currently

#check Rep.Tor

--defined as left derivation (losing canonicality)

end DerivedFunctor

section Ext

--general quasi iso for homological complex
#check HomologicalComplexUpToQuasiIso

--specify to `ℤ` cochain complex
#check DerivedCategory

#check CategoryTheory.ShiftedHom

#check CategoryTheory.Localization.SmallShiftedHom

#check CategoryTheory.Abelian.Ext

--the (very canonical) cup product, but also the ingrediaent to long exact sequence

#check CategoryTheory.ShiftedHom.comp
#check CategoryTheory.Abelian.Ext.comp

--for `Ext X Y 0`

#check CategoryTheory.ShiftedHom.mk₀
#check CategoryTheory.Abelian.Ext.mk₀

--for connecting homomorphism

#check CategoryTheory.ShortComplex.ShortExact.singleδ
#check CategoryTheory.ShortComplex.ShortExact.extClass

--map under exact functor

#check CategoryTheory.Abelian.Ext.mapExactFunctor

#check CategoryTheory.Abelian.Ext.mapExactFunctor_mk₀

#check CategoryTheory.Abelian.Ext.mapExactFunctor_comp

#check CategoryTheory.Abelian.Ext.mapExactFunctor_extClass

section Applications

--sheaf cohomology realized as `Ext`
#check CategoryTheory.Sheaf.H

--homological dimension
#check CategoryTheory.projectiveDimension
#check CategoryTheory.injectiveDimension

end Applications

end Ext

section ModuleCat

--projective
#check Module.Projective
#check CategoryTheory.Projective
#check IsProjective.iff_projective

--injective
#check Module.Injective
#check CategoryTheory.Injective
#check Module.injective_iff_injective_object

#check Module.Baer
#check Module.Baer.extension_property
#check Module.Baer.iff_injective

end ModuleCat

section IsomorphismTheorems

--basic comstructions
#check Ideal.map
#check Ideal.comap
#check Submodule.map
#check Submodule.comap

--basic constructions
#check Submodule.Quotient.mk
#check Submodule.mkQ
#check Ideal.Quotient.mk
#check Ideal.Quotient.mkₐ

#check Submodule.liftQ
#check Ideal.Quotient.lift
#check Ideal.Quotient.liftₐ

#check Submodule.mapQ
#check Ideal.quotientMap
#check Ideal.quotientMapₐ

--first isomorphism theorem and variants
#check RingHom.quotientKerEquivOfSurjective
#check RingHom.quotientKerEquivRange
#check LinearMap.quotKerEquivOfSurjective
#check LinearMap.quotKerEquivRange

--CRT
#check Ideal.quotientInfRingEquivPiQuotient

--second isomorphism theorem
#check LinearMap.quotientInfEquivSupQuotient

--third isomorphism theorem and variant
#check Submodule.quotientQuotientEquivQuotient
#check Submodule.quotientQuotientEquivQuotientSup

end IsomorphismTheorems

section Nakayama

#check Submodule.eq_smul_of_le_smul_of_le_jacobson

end Nakayama

section MorphismHierarchy

--Don't create any new definitions which take a term of a morphism class as an argument!
--https://leanprover.zulipchat.com/#narrow/channel/287929-mathlib4/topic/Mathlib.27s.20morphism.20hierarchy/near/554383157

--there are existing bad things
#check IsLocalHom
#check RingHom.ker

--we already have a decending system through hierarchy

end MorphismHierarchy

section Localization

--implementation of localization

#check IsLocalization
#check Localization
#check Localization.AtPrime

#check IsLocalizedModule
#check LocalizedModule
#check LocalizedModule.AtPrime

--universal property is stated via "is" version

#check IsLocalization.lift

#check IsLocalizedModule.lift

end Localization

section TensorProduct

--implemented as what we usually do
#check TensorProduct

--universal property
#check TensorProduct.lift
#check TensorProduct.lift.unique

--about isomorphisms : use loogle and leansearch

--important ones
#check TensorProduct.lid
#check Algebra.TensorProduct.lid
#check TensorProduct.comm
#check Algebra.TensorProduct.comm
#check TensorProduct.assoc
#check Algebra.TensorProduct.assoc

--"is" version
#check IsTensorProduct
#check IsBaseChange

end TensorProduct

section DimensionTheory

--for ring
#check ringKrullDim
#check Ideal.height

--Krull height theorem
#check Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes
#check Ideal.height_le_spanRank_toENat_of_mem_minimalPrimes

--other useful results
#check Ideal.height_le_spanRank_toENat_of_mem_minimalPrimes
#check Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown

--polynomial
#check Polynomial.ringKrullDim_le
#check Polynomial.ringKrullDim_of_isNoetherianRing

--for module
#check Module.supportDim

--key lemma
#check PrimeSpectrum.exist_ltSeries_mem_one_of_mem_last

#check Module.supportDim_le_supportDim_quotSMulTop_succ_of_mem_jacobson
#check Module.supportDim_quotSMulTop_succ_le_of_notMem_minimalPrimes
#check Module.supportDim_quotSMulTop_succ_eq_supportDim_mem_jacobson

end DimensionTheory

section Completion

#check Ideal.Filtration

#check reesAlgebra

#check Ideal.Filtration.submodule

--Artin-Rees
#check Ideal.exists_pow_inf_eq_pow_smul
--Krull intersection for local ring
#check Ideal.iInf_pow_eq_bot_of_isLocalRing
--Krull intersection for domain
#check Ideal.iInf_pow_eq_bot_of_isDomain

variable (R :Type*) [CommRing R] (I : Ideal R)
--Associated graded
#check (reesAlgebra I) ⧸ I.map (algebraMap R (reesAlgebra I))

end Completion

section Flat

#check Module.Flat

--via fg ideal
#check Module.Flat.iff_rTensor_injective
#check Module.Flat.iff_lTensor_injective

--equational criterion
#check Module.Flat.exists_factorization_of_apply_eq_zero_of_free

--free from flat
#check Module.free_of_flat_of_isLocalRing

end Flat

section Integral

#check Algebra.IsIntegral

--integrally closed, but for fraction ring intead of domain
#check IsIntegrallyClosedIn
#check IsIntegrallyClosed

--GU
#check Ideal.exists_ideal_over_prime_of_isIntegral_of_isPrime

--GD
#check instHasGoingDownOfIsDomainOfFaithfulSMulOfIsIntegralOfIsIntegrallyClosed

end Integral
