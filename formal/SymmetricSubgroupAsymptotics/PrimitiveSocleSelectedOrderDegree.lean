import SymmetricSubgroupAsymptotics.PrimitiveSocleRawONanScott
import SymmetricSubgroupAsymptotics.MinimalNormalIsotypicRelativeOrdinaryGenerators
import SymmetricSubgroupAsymptotics.PerfectSubdirect
import SymmetricSubgroupAsymptotics.PerfectPermutationTwicePrimeOrderDegree
import SymmetricSubgroupAsymptotics.EquivSelectedElementOrder

/-! A selected element in an ABSTRACT actual simple-factor model gives a
degree bound for the ORIGINAL faithful action. All socle axes, perfectness
and order transport are proved with the model type left abstract. Concrete
consumers discharge the element witness with their independently checked
literal source theorem, without expanding model arithmetic in this proof. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.PrimitiveSocleSelectedOrderDegree
open PrimitiveSocleRawStructure

variable {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X]
    [FaithfulSMul G X] (D : NonaffineData G X)

theorem prime_add_four_le_card (M : Type) [Group M] (e : D.Simple ≃* M)
    (p : ℕ) (hp : p.Prime) (hcop : Nat.Coprime 2 p)
    (hwitness : ¬ IsMulCommutative M → ∃ m : M, 2*p ∣ orderOf m) :
    p+4 ≤ Nat.card X := by
  classical
  letI : Fintype X := Fintype.ofFinite X
  have hn : ¬ IsMulCommutative M := by
    intro hc
    apply D.noncommutative
    apply isMulCommutative_iff.mpr
    intro x y
    apply e.injective
    have h := (isMulCommutative_iff.mp hc) (e x) (e y)
    simpa only [map_mul] using h
  let i : Fin D.factorCount := ⟨0,D.factorCount_pos⟩
  let axis : D.Simple →* G := MinimalNormalIsotypicRelativeOrdinaryGenerators.axisHom
    (finiteGroupSocle G) D.socleEquiv i
  have haxis : Function.Injective axis := Subtype.coe_injective.comp
    (MinimalNormalIsotypicRelativeOrdinaryGenerators.axisMap_injective
      (finiteGroupSocle G) D.socleEquiv i)
  letI : Group.IsPerfect D.Simple := simple_perfect_of_nonabelian D.noncommutative
  obtain ⟨g,hg⟩ := EquivSelectedElementOrder.exists_dvd_orderOf e (2*p) (hwitness hn)
  let f : D.Simple →* Equiv.Perm X := (MulAction.toPermHom G X).comp axis
  have hf : Function.Injective f := MulAction.toPerm_injective.comp haxis
  exact PerfectPermutationTwicePrimeOrderDegree.prime_add_four_le_card_of_faithful_action
    f hf g p hp hcop hg

end SymmetricSubgroupAsymptotics.PrimitiveSocleSelectedOrderDegree
