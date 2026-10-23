import SymmetricSubgroupAsymptotics.CFSGUnitaryRankTwoTorus
import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryActionTransport
import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryRankTwoGeneration

/-! A central original derived image commutes with literal natural
upper elements, without scalar ambiguity.  The ambiguity is removed by
the proved defining-characteristic unipotent scalar rigidity. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
open CFSGTwistedANaturalMatrices CFSGTwistedAUpperUnipotent

theorem rankTwoDerivedCover_action (q : CFSG.PrimePower) (hq : 3 ≤ q.order)
    (g : naturalFixed 2 q) :
    twistedDerivedAction 2 q (rankTwoDerivedCover q hq g) =
      naturalElementaryAction (q.Extension 2) 2 g.val := by
  change naturalAction (q.Extension 2) 2
    (CFSGTwistedAIntervalSource.elementaryToModel (q.Extension 2) 2 g.val) = _
  exact CFSGTwistedAIntervalSource.elementaryToModel_action (q.Extension 2) 2 g.val

theorem rankTwo_central_cover_conjugates_upper (q : CFSG.PrimePower) (hq : 3 ≤ q.order)
    (g : naturalFixed 2 q)
    (hg : rankTwoDerivedCover q hq g ∈ Subgroup.center (commutator (Fixed 2 q)))
    (u : naturalUnipotent 2 q) :
    g.val * u.val * g.val⁻¹ = u.val := by
  let v : naturalFixed 2 q := ⟨u.val, u.property.2⟩
  have hc : rankTwoDerivedCover q hq g * rankTwoDerivedCover q hq v *
      (rankTwoDerivedCover q hq g)⁻¹ = rankTwoDerivedCover q hq v := by
    have he := (Subgroup.mem_center_iff.mp hg) (rankTwoDerivedCover q hq v)
    rw [← he, mul_assoc, mul_inv_cancel, mul_one]
  have hh := congrArg (twistedDerivedAction 2 q) hc
  simp only [map_mul, map_inv, rankTwoDerivedCover_action] at hh
  apply upper_conjugate_of_action_eq q 2 (by decide) g.val u u
  simpa only [map_mul, map_inv] using hh

end SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
