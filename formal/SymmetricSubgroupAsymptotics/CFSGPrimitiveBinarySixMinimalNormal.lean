import SymmetricSubgroupAsymptotics.CFSGIsotypicBinarySixProductFactors
import SymmetricSubgroupAsymptotics.CFSGSurjectiveRepresentationIrreducible
import SymmetricSubgroupAsymptotics.PrimitiveSocleHomogeneousMinimalNormal
import SymmetricSubgroupAsymptotics.CFSGNoAbelianNormalRadical

/-! In the remaining homogeneous degree-six case the literal nonabelian
minimal normal subgroup is simple. Its ambient centralizer is soluble,
and hence trivial in the absence of abelian normal subgroups. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical MonoidAlgebra IsMulCommutative

namespace SymmetricSubgroupAsymptotics.CFSGPrimitiveBinarySixMinimalNormal
open CFSGIsotypicRepresentationCoordinates CFSGPrimeBinaryAbelianNormal

variable {G V : Type} [Group G] [Finite G] [AddCommGroup V]
  [Module (ZMod 2) V] [Finite V] [FiniteDimensional (ZMod 2) V]
  (rho : Representation (ZMod 2) G V)

abbrev restriction (E : Subgroup G) : Representation (ZMod 2) E V := rho.comp E.subtype

theorem minimal_normal_isSimple
    (hrho : Representation.IsIrreducible rho) (hf : Function.Injective rho)
    (hd : Module.finrank (ZMod 2) V = 6)
    (E : Subgroup G) (hE : IsMinimalNormalSubgroup E) (hnc : ¬ IsMulCommutative E)
    (hiso : IsIsotypic (ZMod 2)[E] (restriction rho E).asModule) : IsSimpleGroup E := by
  letI : E.Normal := hE.1
  letI : Representation.IsIrreducible rho := hrho
  letI : Nontrivial V := Subrepresentation.irreducible_module_nontrivial rho
  let rhoE : Representation (ZMod 2) E V := restriction rho E
  have hss := CliffordRawRestriction.proved.semisimple rho hrho E
  obtain ⟨n, U, hn, hU, e, he⟩ := exists_irreducible_coordinates rhoE hss hiso
  let tau := U.toRepresentation
  letI : Representation.IsIrreducible tau := hU
  letI : Nontrivial U.toSubmodule := Subrepresentation.irreducible_module_nontrivial tau
  have hfE : Function.Injective rhoE := by
    intro a b hab
    exact Subtype.ext (hf hab)
  have htf : Function.Injective tau := constituent_injective_of_coordinates rhoE tau hfE e he
  have hprod : n * Module.finrank (ZMod 2) U.toSubmodule = 6 := by
    have hh := e.finrank_eq.symm
    rw [Module.finrank_pi_fintype] at hh
    have hdim : n * Module.finrank (ZMod 2) U.toSubmodule = Module.finrank (ZMod 2) V := by
      simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul, Nat.cast_id] using hh
    exact hdim.trans hd
  have hdiv : Module.finrank (ZMod 2) U.toSubmodule ∣ 6 :=
    ⟨n, by simpa only [mul_comm] using hprod.symm⟩
  obtain ⟨C⟩ := PrimitiveSocleONanScottHelpers.chart_of_minimalNormal_nonempty E hE hnc
  let tauP : Representation (ZMod 2) (Fin C.factorCount → C.Simple) U.toSubmodule :=
    tau.comp C.equiv.symm.toMonoidHom
  have hpi : Representation.IsIrreducible tauP :=
    representationIrreducible_of_surjective_equivariant tau tauP
      C.equiv.toMonoidHom (LinearMap.id) Function.surjective_id
      (by intro g v; change tau g v = tau (C.equiv.symm (C.equiv g)) v
          rw [C.equiv.symm_apply_apply]) hU
  have hpf : Function.Injective tauP := by
    intro a b hab
    exact C.equiv.symm.injective (htf hab)
  letI : Subsingleton (Fin C.factorCount) :=
    CFSGIsotypicBinarySixProductFactors.factor_index_subsingleton tauP hpi hpf hdiv
      C.noncommutative
  letI : Unique (Fin C.factorCount) :=
    ⟨⟨0, C.factorCount_pos⟩, fun i => Subsingleton.elim _ _⟩
  exact (C.equiv.trans (MulEquiv.funUnique (Fin C.factorCount) C.Simple)).isSimpleGroup

theorem normal_centralizer_eq_bot
    (hrho : Representation.IsIrreducible rho) (hf : Function.Injective rho)
    (hd : Module.finrank (ZMod 2) V = 6)
    (hNo : ∀ N : Subgroup G, N.Normal → IsMulCommutative N → N = ⊥)
    (E : Subgroup G) [E.Normal] [IsSimpleGroup E] (hnc : ¬ IsMulCommutative E)
    (hiso : IsIsotypic (ZMod 2)[E] (restriction rho E).asModule) :
    Subgroup.centralizer (E : Set G) = ⊥ := by
  letI : Representation.IsIrreducible rho := hrho
  letI : Nontrivial V := Subrepresentation.irreducible_module_nontrivial rho
  let rhoE : Representation (ZMod 2) E V := restriction rho E
  have hfE : Function.Injective rhoE := by
    intro a b hab
    exact Subtype.ext (hf hab)
  have hss := CliffordRawRestriction.proved.semisimple rho hrho E
  have hdiv : Module.finrank (ZMod 2) V ∣ 6 := by rw [hd]
  letI : IsSolvable (CFSGIrreducibleLinearCentralizer.linearCentralizer rhoE) :=
    CFSGIsotypicSimpleCentralizerSix.isotypic_simple_centralizer_soluble
      rhoE hfE hnc hdiv hss hiso
  let D := Subgroup.centralizer (E : Set G)
  have hc (d : D) (a : E) : (d : G) * a = a * d :=
    ((Subgroup.mem_centralizer_iff.mp d.property) a a.property).symm
  letI : IsSolvable D := solvable_of_solvable_injective
    (f := commutingSubgroupHom rho E D hc)
    (commutingSubgroupHom_injective rho hf E D hc)
  exact CFSGNoAbelianNormalRadical.soluble_normal_eq_bot hNo D

end SymmetricSubgroupAsymptotics.CFSGPrimitiveBinarySixMinimalNormal
