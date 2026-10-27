import SymmetricSubgroupAsymptotics.CFSGPSLTwoProductTorusCover

/-! Every coset in the ONE actual correlated index-three cover has a
Borel-power/Weyl-mask representative. No coordinate C3 factors are used. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGPSLTwoCorrelatedCoverMaskRepresentatives
open CFSGPSLTwoGeometry CFSGPSLTwoRootCoordinates CFSGPSLTwoProductTorusCover
variable {F J : Type*} [Field F]

theorem product_two_cells (g : J → PSL (F:=F)) :
    ∃ (s : Set J) (b u : J → projectiveBorel (F:=F)),
      g=borelPowerHom b*weylMask s*borelPowerHom u := by
  classical
  let s : Set J := {i | g i ∉ projectiveBorel (F:=F)}
  have hex (i : J) : ∃ b u : projectiveBorel (F:=F),
      g i=b.val*(weylMask (F:=F) s i)*u.val := by
    by_cases hi : g i ∈ projectiveBorel (F:=F)
    · refine ⟨⟨g i,hi⟩,1,?_⟩
      simp [weylMask,s,hi]
    · obtain ⟨b,u,he⟩ := (two_cells (g i)).resolve_left hi
      refine ⟨b,⟨u.val,projectiveRoot_le_borel u.property⟩,?_⟩
      simpa only [weylMask,s,Set.mem_setOf_eq,hi,not_false_eq_true,if_true] using he
  let b : J → projectiveBorel (F:=F) := fun i => Classical.choose (hex i)
  let u : J → projectiveBorel (F:=F) := fun i => Classical.choose (Classical.choose_spec (hex i))
  refine ⟨s,b,u,?_⟩
  funext i
  have hh := Classical.choose_spec (Classical.choose_spec (hex i))
  by_cases hi : g i ∈ projectiveBorel (F:=F) <;>
    simpa only [Pi.mul_apply,borelPowerHom,MonoidHom.coe_mk,OneHom.coe_mk,
      weylMask,s,Set.mem_setOf_eq,hi,not_true_eq_false,not_false_eq_true,
      if_true,if_false,b,u] using hh

/-- Complete actual cover: every original G/H coset is reached from a
Weyl mask by an element of the original Borel power. -/
theorem every_coset_has_mask_representative [Finite J]
    (H : Subgroup (J → projectiveBorel (F:=F))) [H.Normal]
    (hindex : H.index = 3) (hcop : (Nat.card F).Coprime 3)
    (g : J → PSL (F:=F)) :
    ∃ (s : Set J) (b : J → projectiveBorel (F:=F)),
      (QuotientGroup.mk g : (J → PSL (F:=F)) ⧸ H.map borelPowerHom) =
      QuotientGroup.mk (borelPowerHom b*weylMask s) := by
  classical
  obtain ⟨s,b,u,he⟩ := product_two_cells g
  obtain ⟨n,hn⟩ := exists_product_torus_move H hindex hcop (weylMask s)
    (weylMask_conjugates_torus s) u
  let bn : J → projectiveBorel (F:=F) := fun i =>
    ⟨(n i).val,pairTorus_le_borel (n i).property⟩
  have hbn : borelPowerHom bn=torusPowerHom n := rfl
  have hh := congrArg
    (fun q : (J → PSL (F:=F)) ⧸ H.map borelPowerHom => (borelPowerHom b) • q) hn
  change (QuotientGroup.mk (borelPowerHom b*(torusPowerHom n*weylMask s)) :
      (J → PSL (F:=F)) ⧸ H.map borelPowerHom) =
    QuotientGroup.mk (borelPowerHom b*(weylMask s*borelPowerHom u)) at hh
  refine ⟨s,b*bn,?_⟩
  simpa only [he,map_mul,hbn,mul_assoc] using hh.symm

end SymmetricSubgroupAsymptotics.CFSGPSLTwoCorrelatedCoverMaskRepresentatives
