import SymmetricSubgroupAsymptotics.CFSGPSLTwoProductBorelOrbitLabels
import SymmetricSubgroupAsymptotics.CFSGPSLTwoProductTorusCover

/-! Actual product-Borel cosets, their equivariant product chart, and
Weyl-mask orbit sizes. No correlated cover is identified with a product. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGPSLTwoProductBaseCosetChart
open CFSGPSLTwoGeometry CFSGPSLTwoRootCoordinates CFSGPSLTwoProductTorusCover
variable {F J : Type*} [Field F]

abbrev BaseSpace := (J → PSL (F:=F)) ⧸ (borelPowerHom (F:=F) (J:=J)).range
instance baseAction : MulAction (J → projectiveBorel (F:=F)) (BaseSpace (F:=F) (J:=J)) :=
  MulAction.compHom _ borelPowerHom

def projection : BaseSpace (F:=F) (J:=J) → (J → Points (F:=F)) :=
  Quotient.lift (fun g i => QuotientGroup.mk (g i)) (by
    intro g k hgk
    funext i
    apply QuotientGroup.eq.mpr
    obtain ⟨b,hb⟩ := QuotientGroup.leftRel_apply.mp hgk
    have he : (b i).val=(g i)⁻¹*k i := congrFun hb i
    rw [←he]
    exact (b i).property)

theorem projection_mk (g : J → PSL (F:=F)) :
    projection (QuotientGroup.mk g) = fun i => QuotientGroup.mk (g i) := rfl

theorem projection_injective : Function.Injective (projection (F:=F) (J:=J)) := by
  intro q r
  induction q using Quotient.inductionOn' with
  | h g =>
    induction r using Quotient.inductionOn' with
    | h k =>
      intro he
      apply QuotientGroup.eq.mpr
      let b : J → projectiveBorel (F:=F) := fun i =>
        ⟨(g i)⁻¹*k i,QuotientGroup.eq.mp (congrFun he i)⟩
      exact ⟨b,rfl⟩

theorem projection_surjective : Function.Surjective (projection (F:=F) (J:=J)) := by
  intro x
  refine ⟨QuotientGroup.mk (fun i => (x i).out),?_⟩
  funext i
  exact Quotient.out_eq' (x i)

theorem projection_equivariant (b : J → projectiveBorel (F:=F)) (q : BaseSpace (F:=F) (J:=J)) :
    projection (b • q)=b • projection q := by
  induction q using Quotient.inductionOn' with
  | h g => rfl

def orbitEquiv (g : J → PSL (F:=F)) :
    MulAction.orbit (J → projectiveBorel (F:=F)) (QuotientGroup.mk g : BaseSpace) ≃
      MulAction.orbit (J → projectiveBorel (F:=F)) (fun i => (QuotientGroup.mk (g i) : Points)) := by
  let f := fun y : MulAction.orbit (J → projectiveBorel (F:=F)) (QuotientGroup.mk g : BaseSpace) =>
    (⟨projection y.val,by
      obtain ⟨b,hb⟩ := MulAction.mem_orbit_iff.mp y.property
      exact MulAction.mem_orbit_iff.mpr
        ⟨b,(projection_equivariant b (QuotientGroup.mk g)).symm.trans (congrArg projection hb)⟩⟩ :
      MulAction.orbit (J → projectiveBorel (F:=F)) (fun i => (QuotientGroup.mk (g i) : Points)))
  apply Equiv.ofBijective f
  constructor
  · intro x y he
    exact Subtype.ext (projection_injective (congrArg Subtype.val he))
  · intro z
    obtain ⟨b,hb⟩ := MulAction.mem_orbit_iff.mp z.property
    refine ⟨⟨b • (QuotientGroup.mk g : BaseSpace),MulAction.mem_orbit_iff.mpr ⟨b,rfl⟩⟩,?_⟩
    apply Subtype.ext
    exact (projection_equivariant b (QuotientGroup.mk g)).trans hb

theorem mask_orbit_card [Finite F] [Fintype J] [DecidableEq J] (s : Finset J) :
    Nat.card (MulAction.orbit (J → projectiveBorel (F:=F))
      (QuotientGroup.mk (weylMask (F:=F) (s : Set J)) : BaseSpace)) = (Nat.card F)^s.card := by
  have he : (fun i => (QuotientGroup.mk (weylMask (F:=F) (s : Set J) i) : Points)) =
      CFSGPSLTwoProductBorelOrbitLabels.maskPoint s := by
    funext i
    by_cases hi : i ∈ s <;>
      simp [weylMask,CFSGPSLTwoProductBorelOrbitLabels.maskPoint,hi,
        CFSGPSLTwoBorelTwoOrbits.opposite,CFSGPSLTwoBorelTwoOrbits.base]
  have hc := Nat.card_congr (orbitEquiv (weylMask (F:=F) (s : Set J)))
  rw [he] at hc
  exact hc.trans (CFSGPSLTwoProductBorelOrbitLabels.maskPoint_orbit_card s)

end SymmetricSubgroupAsymptotics.CFSGPSLTwoProductBaseCosetChart
