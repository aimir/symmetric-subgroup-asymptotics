import SymmetricSubgroupAsymptotics.CFSGSymplecticCharTwoScaledClassPacket
import SymmetricSubgroupAsymptotics.CFSGSymplecticBinaryRankThreePauliClassPacket

/-! Complete literal characteristic-two symplectic scaled class packet.
The actual Pauli27 index supplies the former binary rank-three head;
every other parameter uses the checked point/Siegel packet. The full
elementary projective quotient remains literal throughout. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGSymplecticCharTwoCompleteScaledClassPacket
open PrimitiveSocleRawStructure CFSGReduction CFSGSymplecticSerreMatrices

theorem elementary_scaled_class_cube_le_proper_index
    (r : ℕ) (hr : 3 ≤ r) (q : CFSG.PrimePower) (hp : q.prime=2)
    [IsSimpleGroup (elementaryProjective q.Field r)] [Finite (elementaryProjective q.Field r)]
    (hn : ¬IsMulCommutative (elementaryProjective q.Field r))
    (J : Subgroup (elementaryProjective q.Field r)) (hJ : J≠⊤) :
    25*(Nat.card (ConjClasses (elementaryProjective q.Field r))*
      Nat.card (Outer (elementaryProjective q.Field r)))^3 ≤ 3^J.index := by
  by_cases hhead : r=3 ∧ q.order=2
  · rcases hhead with ⟨rfl,hq⟩
    exact CFSGSymplecticBinaryRankThreePauliClassPacket.elementary_scaled_class_cube_le_proper_index
      q hq J hJ
  · exact CFSGSymplecticCharTwoScaledClassPacket.elementary_scaled_class_cube_le_proper_index
      r hr q hp hn hhead J hJ

end SymmetricSubgroupAsymptotics.CFSGSymplecticCharTwoCompleteScaledClassPacket
