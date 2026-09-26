import SymmetricSubgroupAsymptotics.BinaryNormalFiniteEntry
import SymmetricSubgroupAsymptotics.BinaryCarrierOriginal
import SymmetricSubgroupAsymptotics.BinaryCharacterFusion
import SymmetricSubgroupAsymptotics.FusionFiniteMenu

/-! Exact binary finite entries feed the existing original-normalizer fusion
sum. The pair capacity gap and the character counting envelope are derived
from their checked theorems. Pair/carrier counting estimates, character
majorants and same-source moments remain explicit analytic inputs. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical
namespace SymmetricSubgroupAsymptotics

variable {w b q₀ : ℕ} {κ : Type*}
    (carriers : κ → CheckedPermutationCarrier w q₀)
    (U : Subgroup (Equiv.Perm (Fin w))) (hU : IsPGroup 2 U)
    (P : Subgroup (U × Equiv.Perm (Fin b)) → Prop)
    (Φ : {N : Subgroup U // N.Normal} → Subgroup (Equiv.Perm (Fin b)) → ℝ)
    (D : {N : Subgroup U // N.Normal} → ℝ)

include hU in
/-- One original-axis envelope. The pair handler receives its proved actual
capacity gap, not a supplied surrogate dimension. The character branch uses
the actual quotient and its complete automorphism factor. A carrier handler
receives the exact source/axis equations, so `originalQuotientEquiv` and
`transportOriginal_reconstruct` apply with the untouched full exterior. -/
theorem binaryFiniteEntry_axis_envelope
    (hMaroti : NilpotentConjugacyClassInput)
    (hpair : ∀ (N : {N : Subgroup U // N.Normal})
      (C : BinaryPhysicalPairCertificate U N.1),
      (C.localCertificate.coverDegree : ℝ)+2*Module.finrank (ZMod 2) C.physicalCut+
        4*representationSchurCapacity C.physicalRepresentation<w →
      ∀ J, fusionSurvivingEpiCount U P N J≤D N*Φ N J)
    (hcharacter : ∀ (N : {N : Subgroup U // N.Normal})
      (C : BinaryNormalCharacterCriterion (U ⧸ N.1) w) J,
      (Nat.card ((U ⧸ N.1) ≃* (U ⧸ N.1)) : ℝ)*
        (2 : ℝ)^(binaryCharacterSlope C.dimension*(b : ℝ))≤D N*Φ N J)
    (hcarrier : ∀ (N : {N : Subgroup U // N.Normal}) i,
      (carriers i).source=U → (carriers i).axis=N.1.map U.subtype →
      ∀ J, fusionSurvivingEpiCount U P N J≤D N*Φ N J)
    (N : {N : Subgroup U // N.Normal})
    (hentry : BinaryFiniteEntry carriers U N.1)
    (J : Subgroup (Equiv.Perm (Fin b))) :
    fusionSurvivingEpiCount U P N J≤D N*Φ N J := by
  apply BinaryFiniteEntry.elim hentry
  · intro C
    exact hpair N C (C.actual_gap hU) J
  · intro C
    exact (binaryCharacter_physicalAxis_envelope hMaroti U hU P N C J).trans
      (hcharacter N C J)
  · intro i hs ha
    exact hcarrier N i hs ha J

include hU in
/-- A complete typed entry for every original normal gives the finite-menu
physical bound once the remaining branch estimates and moments are proved.
The original action normalizer divides the whole stable sum; no individual
axis or menu branch is assumed to be normalizer-fixed. This is a theorem for
the displayed original action, not an unproved cover of all finite actions. -/
theorem binaryFiniteEntry_finite_menu
    (hMaroti : NilpotentConjugacyClassInput)
    (hentries : ∀ N : {N : Subgroup U // N.Normal}, BinaryFiniteEntry carriers U N.1)
    (hP : FusionOrbitNatural U P)
    (t M : {N : Subgroup U // N.Normal} → ℝ)
    (q : {N : Subgroup U // N.Normal} → ℕ)
    (hD : ∀ N, 0≤D N) (ht : ∀ N, 0<t N)
    (hΦ : ∀ N J, 0≤Φ N J)
    (hpair : ∀ (N : {N : Subgroup U // N.Normal})
      (C : BinaryPhysicalPairCertificate U N.1),
      (C.localCertificate.coverDegree : ℝ)+2*Module.finrank (ZMod 2) C.physicalCut+
        4*representationSchurCapacity C.physicalRepresentation<w →
      ∀ J, fusionSurvivingEpiCount U P N J≤D N*Φ N J)
    (hcharacter : ∀ (N : {N : Subgroup U // N.Normal})
      (C : BinaryNormalCharacterCriterion (U ⧸ N.1) w) J,
      (Nat.card ((U ⧸ N.1) ≃* (U ⧸ N.1)) : ℝ)*
        (2 : ℝ)^(binaryCharacterSlope C.dimension*(b : ℝ))≤D N*Φ N J)
    (hcarrier : ∀ (N : {N : Subgroup U // N.Normal}) i,
      (carriers i).source=U → (carriers i).axis=N.1.map U.subtype →
      ∀ J, fusionSurvivingEpiCount U P N J≤D N*Φ N J)
    (hq : ∀ N, 1≤q N)
    (hmoment : ∀ N, (∑ J : Subgroup (Equiv.Perm (Fin b)), Φ N J^(q N))≤M N) :
    (Nat.card (FusionOrbitFamily U (FusionAcceptedOrbitPredicate U P)) : ℝ)≤
      ((w+b).factorial : ℝ) /
        (b.factorial * (Nat.card (Subgroup.normalizer (U : Set (Equiv.Perm (Fin w)))) : ℝ)) *
      ∑ N : {N : Subgroup U // N.Normal},
        (D N/(t N)^(q N-1)*M N+(subgroupCount b : ℝ)*D N*t N) := by
  apply fusionPhysical_finite_menu_degree U b P hP Φ D t M q hD ht hΦ
  · intro N J
    exact binaryFiniteEntry_axis_envelope carriers U hU P Φ D hMaroti
      hpair hcharacter hcarrier N (hentries N) J
  · exact hq
  · exact hmoment

end SymmetricSubgroupAsymptotics
