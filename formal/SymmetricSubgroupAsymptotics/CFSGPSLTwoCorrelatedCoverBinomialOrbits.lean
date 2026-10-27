import SymmetricSubgroupAsymptotics.CFSGPSLTwoCorrelatedCoverOrbitSizes
import SymmetricSubgroupAsymptotics.FiniteSubsetBinomialIndex

/-! Complete binomial orbit geometry on ONE original correlated G/H.
No minimally-transitive classification or Tracey input is assumed. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGPSLTwoCorrelatedCoverBinomialOrbits
open CFSGPSLTwoGeometry CFSGPSLTwoRootCoordinates CFSGPSLTwoProductTorusCover
open CFSGPSLTwoCorrelatedCoverProjection
variable {F J : Type} [Field F] [Finite F] [Fintype J] [DecidableEq J]

def index (H : Subgroup (J → projectiveBorel (F:=F))) [H.Normal]
    (hindex : H.index = 3) (hcop : (Nat.card F).Coprime 3) :
    MulAction.orbitRel.Quotient (J → projectiveBorel (F:=F)) (Cover H) ≃
      (Σ k : Fin (Fintype.card J+1), Fin ((Fintype.card J).choose k.val)) :=
  (CFSGPSLTwoCorrelatedCoverOrbitLabels.orbitLabels H hindex hcop).trans
    (FiniteSubsetBinomialIndex.index J)

theorem orbit_card (H : Subgroup (J → projectiveBorel (F:=F))) [H.Normal]
    (hindex : H.index = 3) (hcop : (Nat.card F).Coprime 3)
    (o : MulAction.orbitRel.Quotient (J → projectiveBorel (F:=F)) (Cover H)) :
    Nat.card o.orbit = 3*(Nat.card F)^((index H hindex hcop o).1.val) := by
  let L := CFSGPSLTwoCorrelatedCoverOrbitLabels.orbitLabels H hindex hcop
  let s : Set J := L o
  let sf : Finset J := s.toFinset
  have hs : (sf : Set J)=s := s.coe_toFinset
  have hi : (index H hindex hcop o).1.val=sf.card :=
    FiniteSubsetBinomialIndex.index_rank J s
  have ho : o=Quotient.mk _ (QuotientGroup.mk (weylMask (F:=F) (sf : Set J)) : Cover H) := by
    apply L.injective
    change s=L (Quotient.mk _ (QuotientGroup.mk (weylMask (F:=F) (sf : Set J)) : Cover H))
    rw [CFSGPSLTwoCorrelatedCoverOrbitLabels.orbitLabels_mk]
    have hw := CFSGPSLTwoBorelTwoOrbits.opposite_ne_base (F:=F)
    change (QuotientGroup.mk (projectiveWeyl (F:=F)) : Points (F:=F)) ≠ QuotientGroup.mk 1 at hw
    ext i
    by_cases hmem : i ∈ sf <;>
      simp [label,projection_mk,weylMask,←hs,hmem,CFSGPSLTwoBorelTwoOrbits.base,hw]
  rw [hi,ho]
  change Nat.card (MulAction.orbit (J → projectiveBorel (F:=F))
    (QuotientGroup.mk (weylMask (F:=F) (sf : Set J)) : Cover H))=3*(Nat.card F)^sf.card
  exact CFSGPSLTwoCorrelatedCoverOrbitSizes.mask_orbit_card H hindex hcop sf

theorem orbit_count (H : Subgroup (J → projectiveBorel (F:=F))) [H.Normal]
    (hindex : H.index = 3) (hcop : (Nat.card F).Coprime 3) :
    Nat.card (MulAction.orbitRel.Quotient (J → projectiveBorel (F:=F)) (Cover H)) =
      2^Fintype.card J := by
  have hc := Nat.card_congr (CFSGPSLTwoCorrelatedCoverOrbitLabels.orbitLabels H hindex hcop)
  simpa only [Nat.card_eq_fintype_card,Fintype.card_set] using hc

end SymmetricSubgroupAsymptotics.CFSGPSLTwoCorrelatedCoverBinomialOrbits
