import SymmetricSubgroupAsymptotics.CFSGOrthogonalDAutomorphismCardinality
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDCenterCardinality
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIsometryIndexCardinality
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDProjectiveCenter
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDProjectiveRealization
import SymmetricSubgroupAsymptotics.CFSGOuterCardinalityCancellation
import SymmetricSubgroupAsymptotics.CFSGSimpleIndexTransport

/-! Actual inner/outer cancellation for the SAME original D projective
model in rank at least five. The point-image order, actual O/E index and
literal elementary centre give |Out| <= 8|Aut(K)|, uniformly in
characteristic, without a named orthogonal automorphism theorem. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDOuterCardinality
open CFSGOrthogonalDSerreMatrices CFSGOrthogonalDIndexQuadraticForm
open PrimitiveSocleRawStructure
variable (K : Type) [Field K] [Finite K]

theorem outer_card_le_eight_fieldAut (p : ℕ) [Fact p.Prime] [CharP K p]
    (s : ℕ) [IsSimpleGroup (elementaryProjective K (s+5))] :
    Nat.card (Outer (elementaryProjective K (s+5)))≤8*Nat.card (K≃+*K) := by
  let E := elementaryRootGroup K (s+5)
  let G := elementaryProjective K (s+5)
  let Z := Subgroup.center E
  letI : Finite G := Finite.of_surjective (QuotientGroup.mk' Z) (QuotientGroup.mk'_surjective Z)
  have hn : ¬IsMulCommutative G := by
    intro hcomm
    have ht : Subgroup.center G=⊤ := Subgroup.center_eq_top_iff.mpr hcomm
    have hb : Subgroup.center G=⊥ := elementaryProjective_center_eq_bot K (s+1)
    exact bot_ne_top (hb.symm.trans ht)
  have hZ : Nat.card Z≤2 := CFSGOrthogonalDCenterCardinality.center_card_le_two K (s+1)
  have hcard := Z.card_mul_index
  change Nat.card Z*Nat.card G=Nat.card E at hcard
  have hE : Nat.card E≤2*Nat.card G := hcard.symm.trans_le (Nat.mul_le_mul_right _ hZ)
  have hO : Nat.card (quadraticPreserving K (s+5))≤8*Nat.card G := by
    calc
      Nat.card (quadraticPreserving K (s+5))≤4*Nat.card E :=
        CFSGOrthogonalDIsometryIndexCardinality.quadratic_card_le_four_mul_elementary K (s+1)
      _ ≤4*(2*Nat.card G) := Nat.mul_le_mul_left _ hE
      _ =8*Nat.card G := by omega
  have hAut : Nat.card (MulAut G)≤Nat.card G*(8*Nat.card (K≃+*K)) := by
    calc
      Nat.card (MulAut G)≤Nat.card (quadraticPreserving K (s+5))*Nat.card (K≃+*K) :=
        CFSGOrthogonalDAutomorphismCardinality.automorphism_card_le_quadratic_mul_field K p s
      _ ≤(8*Nat.card G)*Nat.card (K≃+*K) := Nat.mul_le_mul_right _ hO
      _ =Nat.card G*(8*Nat.card (K≃+*K)) := by ac_rfl
  exact CFSGOuterCardinalityCancellation.outer_card_le_of_automorphism_bound hn _ hAut

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDOuterCardinality

namespace SymmetricSubgroupAsymptotics.CFSGReduction
open CFSGOrthogonalDSerreMatrices PrimitiveSocleRawStructure

theorem typeD_high_outer_card_le (r : ℕ) (hr : 5≤r) (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.D r q)] :
    Nat.card (Outer (CFSG.Models.D r q))≤8*Nat.card (q.Field≃+*q.Field) := by
  obtain ⟨s,rfl⟩ : ∃s : ℕ,r=s+5 := ⟨r-5,by omega⟩
  let e := serreProjectiveEquivElementaryProjective q.Field (s+1)
  letI : IsSimpleGroup (elementaryProjective q.Field (s+5)) := e.symm.isSimpleGroup
  rw [outer_card_congr e]
  exact CFSGOrthogonalDOuterCardinality.outer_card_le_eight_fieldAut q.Field q.prime s

end SymmetricSubgroupAsymptotics.CFSGReduction
