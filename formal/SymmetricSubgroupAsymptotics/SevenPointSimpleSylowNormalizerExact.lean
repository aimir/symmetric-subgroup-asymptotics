import SymmetricSubgroupAsymptotics.SevenCycleOddInverter
import SymmetricSubgroupAsymptotics.ConjugateInverseCyclicNormalizerWitness
import SymmetricSubgroupAsymptotics.PrimeCycleParityNormalizer

/-! Exact normalizer21 for a prime-order Sylow7 in an actual faithful
seven-point NONABELIAN SIMPLE source. No assertion that an arbitrary
original overgroup of this simple source is even is made. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.SevenPointSimpleSylowNormalizerExact
local instance : Fact (Nat.Prime 7) := ⟨by decide⟩
local instance : Fact (Nat.Prime 3) := ⟨by decide⟩

theorem normalizer_card_eq_twentyOne {G : Type} [Group G] [Finite G]
    [IsSimpleGroup G] [MulAction G (Fin 7)] [FaithfulSMul G (Fin 7)]
    (hn : ¬IsMulCommutative G) (P : Sylow 7 G) (hP : Nat.card P=7) :
    Nat.card (Subgroup.normalizer (P : Set G))=21 := by
  obtain ⟨g,hg⟩ := exists_prime_orderOf_dvd_card' (G := P) 7 (by rw [hP])
  let a : G := g.val
  have ho : orderOf a=7 := (Subgroup.orderOf_coe g).trans hg
  have hle : Subgroup.zpowers a≤(P : Subgroup G) :=
    (Subgroup.zpowers_le).mpr g.property
  have hgen : (P : Subgroup G)=Subgroup.zpowers a := by
    symm
    apply Subgroup.eq_of_le_of_card_ge hle
    rw [Nat.card_zpowers,ho,hP]
  let rho := MulAction.toPermHom G (Fin 7)
  have hgo : orderOf (rho a)=7 :=
    (orderOf_injective rho (show Function.Injective rho from MulAction.toPerm_injective) a).trans ho
  have hc : (rho a).IsCycle := Equiv.Perm.isCycle_of_prime_order'
    (by rw [hgo]; decide) (by rw [hgo]; decide)
  have hsupport : (rho a).support.card=7 := hc.orderOf.symm.trans hgo
  have htype : (rho a).cycleType={7} := by rw [hc.cycleType,hsupport]
  obtain ⟨sigma,hsigma,hodd⟩ := SevenCycleOddInverter.exists_odd_inverter (rho a) hgo
  exact PrimeCycleParityNormalizer.normalizer_card_eq_prime_half hn P hP a hgen
    (Or.inl rfl) htype (by decide : 7-1=2*3) sigma
    (ConjugateInverseCyclicNormalizerWitness.mem_normalizer_zpowers sigma (rho a) hsigma) hodd

end SymmetricSubgroupAsymptotics.SevenPointSimpleSylowNormalizerExact
