import SymmetricSubgroupAsymptotics.Selected1542SecondMonolith
import SymmetricSubgroupAsymptotics.Selected1542RetainedQuotient
import SymmetricSubgroupAsymptotics.MonolithicCompleteQuotientReduction
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoQuotientEnvelopeTransport

/-! Two actual monolithic reductions end at the SAME original quotient N8.
The third isomorphism is exact; no multiplicity or normal-menu premise enters. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.Selected1542QuotientStructure

local instance twoLayer_secondAxisNormal :
    (show Subgroup (Original ⧸ originalFirstAxis) from secondAxis).Normal := secondAxis_normal

def twoLayerQuotientEquiv : (FirstQuotient ⧸ secondAxis) ≃* Quotient :=
  QuotientGroup.quotientQuotientEquivQuotient originalFirstAxis originalNormal
    originalFirstAxis_le_originalNormal

theorem original_complete_weight_two_layers {b : ℕ}
    (J : Subgroup (Equiv.Perm (Fin b))) :
    completeQuotientWeight (R := Original) J≤
      (Nat.card (GroupEpimorphism J Original) : ℝ)+
        (Nat.card (GroupEpimorphism J FirstQuotient) : ℝ)+
          completeQuotientWeight (R := Quotient) J := by
  have h := MonolithicCompleteQuotientReduction.complete_weight_le_two originalFirstAxis
    (fun N hNN hN => original_first_monolith N hNN hN) secondAxis
    (fun N hNN hN => original_second_monolith N hNN hN) J
  change completeQuotientWeight (R := Original) J≤
    (Nat.card (GroupEpimorphism J Original) : ℝ)+
      (Nat.card (GroupEpimorphism J FirstQuotient) : ℝ)+
        completeQuotientWeight (R := FirstQuotient ⧸ secondAxis) J at h
  rw [Non2UnipotentPrefixFiniteMenu.completeQuotientWeight_congr twoLayerQuotientEquiv J] at h
  exact h

end SymmetricSubgroupAsymptotics.Selected1542QuotientStructure
