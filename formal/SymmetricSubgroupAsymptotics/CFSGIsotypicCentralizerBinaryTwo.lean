import SymmetricSubgroupAsymptotics.CFSGIsotypicCentralizerMultiplicity
import SymmetricSubgroupAsymptotics.CFSGLinearBlockOrderSelected
import SymmetricSubgroupAsymptotics.PrimitiveAffineBottomFibre
import SymmetricSubgroupAsymptotics.PrimitiveSmallExceptionalSocleFactors

/-! The faithful noncommutative three-dimensional constituent has only
scalar intertwiners. Its twofold isotypic centralizer therefore has order
dividing six and is soluble. No classification of six-dimensional linear
groups is an input. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical MonoidAlgebra
namespace SymmetricSubgroupAsymptotics.CFSGIsotypicCentralizerBinaryTwo
open CFSGIrreducibleLinearCentralizer CFSGIsotypicCentralizerMultiplicity

theorem intertwiner_finrank_one_of_irreducible_faithful_three
    {k S W : Type} [Field k] [Finite k] [Group S]
    [AddCommGroup W] [Module k W] [FiniteDimensional k W]
    (tau : Representation k S W) (hirr : Representation.IsIrreducible tau)
    (hf : Function.Injective tau) (hnc : ¬ IsMulCommutative S)
    (hd : Module.finrank k W = 3) :
    Module.finrank k (tau.IntertwiningMap tau) = 1 := by
  letI : Representation.IsIrreducible tau := hirr
  letI : Module k[S] tau.asModule := Representation.instModuleMonoidAlgebraAsModule tau
  letI : IsScalarTower k k[S] tau.asModule :=
    inferInstanceAs (IsScalarTower k k[S] (Representation.asModule tau))
  letI : IsSimpleModule k[S] tau.asModule :=
    (Representation.irreducible_iff_isSimpleModule_asModule tau).mp hirr
  letI : Nontrivial tau.asModule := IsSimpleModule.nontrivial k[S] tau.asModule
  letI : FiniteDimensional k tau.asModule :=
    FiniteDimensional.of_injective tau.asModuleEquiv.toLinearMap tau.asModuleEquiv.injective
  have ht := schur_simple_finrank_tower (k:=k) (R:=k[S]) (X:=tau.asModule)
  have hd2 := two_le_schurRank_of_irreducible_faithful_noncommutative tau hirr hf hnc
  have hdim : Module.finrank k tau.asModule = 3 := tau.asModuleEquiv.finrank_eq.trans hd
  have he : Module.finrank k (Module.End k[S] tau.asModule) = 1 := by
    let f := Module.finrank k (Module.End k[S] tau.asModule)
    let d := Module.finrank (Module.End k[S] tau.asModule) tau.asModule
    have hprod : f*d = 3 := ht.symm.trans hdim
    have hfpos : 0 < f := by nlinarith
    have hdge : 2 ≤ d := hd2
    have hfle : f ≤ 1 := by nlinarith
    omega
  exact (Representation.IntertwiningMap.equivAlgEnd tau).toLinearEquiv.finrank_eq.trans he

theorem binary_twofold_centralizer_card_dvd_six
    {S W : Type} [Group S] [AddCommGroup W] [Module (ZMod 2) W]
    [Finite W] [Nontrivial W] [FiniteDimensional (ZMod 2) W]
    (tau : Representation (ZMod 2) S W) (hirr : Representation.IsIrreducible tau)
    (hf : Function.Injective tau) (hnc : ¬ IsMulCommutative S)
    (hd : Module.finrank (ZMod 2) W = 3) :
    Nat.card (linearCentralizer (repeated (I:=Fin 2) tau)) ∣ 6 := by
  have h := centralizer_card_dvd_multiplicity_of_finrank_one (I:=Fin 2) tau
    (intertwiner_finrank_one_of_irreducible_faithful_three tau hirr hf hnc hd)
  rw [CFSGLinearBlockOrderSelected.binary_linearEquiv_card] at h
  have hs : fullLinearOrder 2 2 = 6 := by decide +kernel
  rwa [hs] at h

theorem binary_twofold_centralizer_soluble
    {S W : Type} [Group S] [AddCommGroup W] [Module (ZMod 2) W]
    [Finite W] [Nontrivial W] [FiniteDimensional (ZMod 2) W]
    (tau : Representation (ZMod 2) S W) (hirr : Representation.IsIrreducible tau)
    (hf : Function.Injective tau) (hnc : ¬ IsMulCommutative S)
    (hd : Module.finrank (ZMod 2) W = 3) :
    IsSolvable (linearCentralizer (repeated (I:=Fin 2) tau)) := by
  letI : Finite (linearCentralizer (repeated (I:=Fin 2) tau)) :=
    Finite.of_injective (fun e : linearCentralizer (repeated (I:=Fin 2) tau) =>
      (e.val : (Fin 2 → W) → (Fin 2 → W))) (by
        intro e f he
        apply Subtype.ext
        exact LinearEquiv.ext (congrFun he))
  exact isSolvable_of_card_dvd_small_head_degree 6 (Or.inl rfl)
    (binary_twofold_centralizer_card_dvd_six tau hirr hf hnc hd)

end SymmetricSubgroupAsymptotics.CFSGIsotypicCentralizerBinaryTwo
