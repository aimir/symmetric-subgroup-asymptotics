import SymmetricSubgroupAsymptotics.CosetOrbitFibreScaling
import SymmetricSubgroupAsymptotics.CFSGPSLTwoCorrelatedCoverOrbitLabels
import SymmetricSubgroupAsymptotics.CFSGPSLTwoProductBaseCosetChart

/-! Exact3*p^k orbit sizes on the actual correlated index-three cover. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGPSLTwoCorrelatedCoverOrbitSizes
open CFSGPSLTwoGeometry CFSGPSLTwoRootCoordinates CFSGPSLTwoProductTorusCover
open CFSGPSLTwoCorrelatedCoverProjection
variable {F J : Type} [Field F] [Finite F] [Fintype J] [DecidableEq J]

theorem borelPowerHom_injective : Function.Injective (borelPowerHom (F:=F) (J:=J)) := by
  intro b c he
  funext i
  exact Subtype.ext (congrFun he i)

/-- The multiplier3 is the original H.index, paid by the actual
stabilizer-filled fibre; it is not assumed independently in every factor. -/
theorem mask_orbit_card
    (H : Subgroup (J → projectiveBorel (F:=F))) [H.Normal]
    (hindex : H.index = 3) (hcop : (Nat.card F).Coprime 3) (s : Finset J) :
    Nat.card (MulAction.orbit (J → projectiveBorel (F:=F))
      (QuotientGroup.mk (weylMask (F:=F) (s : Set J)) : Cover H)) =
      3*(Nat.card F)^s.card := by
  let g := weylMask (F:=F) (s : Set J)
  have hfill (b : J → projectiveBorel (F:=F)) :
      ∃ a : J → projectiveBorel (F:=F),
        (QuotientGroup.mk (borelPowerHom a*g) : Cover H) =
          QuotientGroup.mk (g*borelPowerHom b) := by
    obtain ⟨n,hn⟩ := exists_product_torus_move H hindex hcop g
      (weylMask_conjugates_torus (s : Set J)) b
    let a : J → projectiveBorel (F:=F) := fun i =>
      ⟨(n i).val,pairTorus_le_borel (n i).property⟩
    refine ⟨a,?_⟩
    change (QuotientGroup.mk (torusPowerHom n*g) : Cover H) =
      QuotientGroup.mk (g*borelPowerHom b)
    exact hn
  have hs := CosetOrbitFibreScaling.card_orbit_eq_index_mul
    (borelPowerHom (F:=F) (J:=J)) borelPowerHom_injective H g hfill
  have hb := CFSGPSLTwoProductBaseCosetChart.mask_orbit_card (F:=F) s
  change Nat.card (MulAction.orbit (J → projectiveBorel (F:=F))
    (QuotientGroup.mk g : Cover H)) = _ at hs
  rw [hindex,hb] at hs
  exact hs

end SymmetricSubgroupAsymptotics.CFSGPSLTwoCorrelatedCoverOrbitSizes
