import SymmetricSubgroupAsymptotics.CFSGUnitaryRadicalFrattiniOrdinaryGenerators
import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCentralRoot
import SymmetricSubgroupAsymptotics.CFSGUnitaryRankThreeUpperShear

/-! A literal central transvection in the actual binary rank-two middle
upper group shears the three-coordinate rank-four radical. The SAME
upper factorization and actual ambient Frattini kernel are retained. -/
set_option autoImplicit false
noncomputable section
open scoped Matrix commutatorElement
namespace SymmetricSubgroupAsymptotics.CFSGUnitaryRankFourUpperShear
open CFSGTwistedANaturalMatrices CFSGTwistedAUpperUnipotent
open CFSGTwistedAUnitaryCoordinates CFSGTwistedAUnitaryNaturalRadical
open CFSGSerreOrdinaryTwists

theorem central_one_condition (q : CFSG.PrimePower) (hq : q.order = 2) :
    Condition q 0 0 (1 : q.Extension 2) := by
  letI : Fact q.prime.Prime := ⟨q.prime_isPrime⟩
  have hp : q.prime = 2 := by
    have hle := Nat.le_self_pow q.exponent_pos.ne' q.prime
    change q.prime ≤ q.order at hle
    have hlo := q.prime_isPrime.two_le
    omega
  have htwo : (2 : q.Extension 2) = 0 := by
    simpa only [hp] using (CharP.cast_eq_zero (q.Extension 2) q.prime)
  apply (centralCondition_iff q 0 1).mpr
  simpa only [map_one,CFSGTwistedAUnitaryNaturalRadical.parity,pow_zero,one_mul,one_add_one_eq_two] using htwo

def middleShear (q : CFSG.PrimePower) (hq : q.order = 2) : naturalUnipotent 2 q :=
  radicalUpperHom q 0 (centralRadicalElement q 0
    ⟨1,(centralCondition_iff q 0 1).mp (central_one_condition q hq)⟩)

theorem middleShear_matrix (q : CFSG.PrimePower) (hq : q.order = 2) :
    ((middleShear q hq).val.val : Mat (q.Extension 2) 2) =
      1+Matrix.single (0 : Fin 3) 2 (1 : q.Extension 2) := by
  change ((radicalElement q 0 0 1
    (centralParameters_condition q 0 1 ((centralCondition_iff q 0 1).mp
      (central_one_condition q hq)))).val.val : Mat (q.Extension 2) 2) = _
  exact radicalCentral_matrix q 0 1 _

def radicalConjugate (q : CFSG.PrimePower) (hq : q.order = 2)
    (z : fixedRadical q 2) : fixedRadical q 2 :=
  radicalMiddleConjugate q 2 (upperFixedHom q 2 (middleShear q hq)) z

theorem conjugate_apply (q : CFSG.PrimePower) (hq : q.order = 2) (z : fixedRadical q 2) :
    radicalUpperHom q 2 (radicalConjugate q hq z) =
      middleUnipotentHom q 2 (middleShear q hq)*radicalUpperHom q 2 z*
        (middleUnipotentHom q 2 (middleShear q hq))⁻¹ := by
  apply upperFixedHom_injective q 4
  rfl

theorem parameter_conjugate (q : CFSG.PrimePower) (hq : q.order = 2) (z : fixedRadical q 2) :
    (fixedRadicalParameterHom q 2 (radicalConjugate q hq z)).toAdd =
      (fixedRadicalParameterHom q 2 z).toAdd+
        Pi.single 0 ((fixedRadicalParameterHom q 2 z).toAdd 2) := by
  rw [radicalConjugate,fixedRadicalParameter_middle_conjugate]
  let v := (fixedRadicalParameterHom q 2 z).toAdd
  change ((middleShear q hq).val.val : Mat (q.Extension 2) 2) *ᵥ v = v+Pi.single 0 (v 2)
  rw [middleShear_matrix,Matrix.add_mulVec,Matrix.one_mulVec,Matrix.single_mulVec]
  simp only [one_mul]
  congr 1

theorem ranges_generate (q : CFSG.PrimePower) :
    (radicalUpperHom q 2).range ⊔ (middleUnipotentHom q 2).range = ⊤ := by
  apply top_unique
  intro g _
  obtain ⟨⟨u,m⟩,rfl⟩ := upperProduct_surjective q 2 g
  change radicalUpperHom q 2 u*middleUnipotentHom q 2 m ∈
    (radicalUpperHom q 2).range ⊔ (middleUnipotentHom q 2).range
  exact Subgroup.mul_mem _
    ((show (radicalUpperHom q 2).range ≤
      (radicalUpperHom q 2).range ⊔ (middleUnipotentHom q 2).range from le_sup_left) ⟨u,rfl⟩)
    ((show (middleUnipotentHom q 2).range ≤
      (radicalUpperHom q 2).range ⊔ (middleUnipotentHom q 2).range from le_sup_right) ⟨m,rfl⟩)

theorem radical_kernel_image_mem_frattini (q : CFSG.PrimePower) (s : ℕ)
    (z : fixedRadical q s) (hz : z ∈ (fixedRadicalParameterHom q s).ker) :
    radicalUpperHom q s z ∈ frattini (naturalUnipotent (s+2) q) := by
  letI : Fact q.prime.Prime := ⟨q.prime_isPrime⟩
  have hcard : Nat.card (naturalUnipotent (s+2) q) =
      q.prime^(q.exponent*((s+2)*(s+3)/2)) := by
    rw [naturalUnipotent_card]
    change (q.prime^q.exponent)^((s+2)*(s+3)/2) = _
    rw [pow_mul]
  have hp : IsPGroup q.prime (naturalUnipotent (s+2) q) := IsPGroup.of_card hcard
  have hcomm : commutator (naturalUnipotent (s+2) q) ≤ frattini (naturalUnipotent (s+2) q) := by
    rw [←primeAbelianizationGroupMap_ker q.prime (naturalUnipotent (s+2) q) hp]
    exact Abelianization.commutator_subset_ker _
  obtain ⟨c,hc⟩ := exists_centralRadical_of_parameter_one q s z hz
  obtain ⟨x,y,hxy⟩ := centralRadical_eq_commutator q s c
  have he : radicalUpperHom q s z =
      ⁅radicalUpperHom q s x,radicalUpperHom q s y⁆ := by
    rw [←map_commutatorElement,hxy,hc]
  rw [he]
  exact hcomm (Subgroup.commutator_mem_commutator
    (Subgroup.mem_top _) (Subgroup.mem_top _))

end SymmetricSubgroupAsymptotics.CFSGUnitaryRankFourUpperShear
