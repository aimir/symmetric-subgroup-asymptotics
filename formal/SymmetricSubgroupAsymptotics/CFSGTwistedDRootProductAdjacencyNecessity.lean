import SymmetricSubgroupAsymptotics.CFSGTwistedDProjectiveAmbientEmbedding
import SymmetricSubgroupAsymptotics.CFSGTwistedDFixedScalarSpanDescent
import SymmetricSubgroupAsymptotics.CFSGTwoPlaneIntersectionPartition

/-! The intrinsic commuting/root-product test forces adjacency of the
SAME actual fixed-field singular planes. Relative root lines only map
into ambient root lines; actual scalar-span descent reflects the
nonzero intersection, and quadratic values descend on fixed vectors. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTwistedDRootProductAdjacencyNecessity
open CFSGOrthogonalDSerreMatrices CFSGTwistedDRelativeElementaryGroup
open CFSGTwistedDRelativeUnipotentSylow CFSGTwistedDProjectiveUnipotent
open CFSGTwistedDProjectiveRootFamily CFSGTwistedDProjectivePlaneLabel
open CFSGTwistedDIntrinsicRootProduct CFSGTwistedDProjectiveAmbientEmbedding
open CFSGTwistedDDisplacementScalarSpan CFSGTwistedDFixedScalarSpanDescent
open CFSGTwistedDSingularPlaneOrbit CFSGTwistedDFixedQuadraticSpace
open CFSGTwistedA2FixedField

theorem root_product_forces_adjacency (s : ℕ) (q : CFSG.PrimePower)
    (g h : relativeRootGroup (s + 2) q)
    (hne : conjugateRootPlane s q g ≠ conjugateRootPlane s q h)
    (hr : RootProductRelation s q
      (projectiveConjugateRootLine s q (projection s q g))
      (projectiveConjugateRootLine s q (projection s q h))) :
    Module.finrank (fixedField q)
        (conjugateRootPlane s q g ⊓ conjugateRootPlane s q h :
          Submodule (fixedField q) (fixedSpace (s + 2) q)) = 1 ∧
      ∀ z ∈ conjugateRootPlane s q g ⊔ conjugateRootPlane s q h,
        fixedQuadraticForm (s + 2) q z = 0 := by
  letI : Module.Finite (fixedField q) (fixedSpace (s + 2) q) := Module.Finite.of_finite
  let G := CFSGOrthogonalDIndexPlaneRootLine.conjugateRootPlane (q.Extension 2) s
    (relativeInclusion s q g)
  let H := CFSGOrthogonalDIndexPlaneRootLine.conjugateRootPlane (q.Extension 2) s
    (relativeInclusion s q h)
  have hG : scalarSpan (s + 2) q (conjugateRootPlane s q g) = G :=
    conjugateRootPlane_scalarSpan s q g
  have hH : scalarSpan (s + 2) q (conjugateRootPlane s q h) = H :=
    conjugateRootPlane_scalarSpan s q h
  have hneK : G ≠ H := by
    intro he
    exact hne (scalarSpan_injective (s + 2) q (hG.trans (he.trans hH.symm)))
  obtain ⟨x, hx, hxn, y, hy, hyn, hc, hp⟩ := hr
  have hxp := projectiveRootLine_image_le_ambient s q g
    (show projectiveAmbientHom s q x ∈
      (projectiveConjugateRootLine s q (projection s q g)).map
        (projectiveAmbientHom s q) from ⟨x, hx, rfl⟩)
  have hyp := projectiveRootLine_image_le_ambient s q h
    (show projectiveAmbientHom s q y ∈
      (projectiveConjugateRootLine s q (projection s q h)).map
        (projectiveAmbientHom s q) from ⟨y, hy, rfl⟩)
  have hxm : projectiveAmbientHom s q x ≠ 1 := by
    intro he
    exact hxn (projectiveAmbientHom_injective s q (he.trans (map_one _).symm))
  have hym : projectiveAmbientHom s q y ≠ 1 := by
    intro he
    exact hyn (projectiveAmbientHom_injective s q (he.trans (map_one _).symm))
  have hcm : Commute (projectiveAmbientHom s q x) (projectiveAmbientHom s q y) := by
    change projectiveAmbientHom s q x * projectiveAmbientHom s q y =
      projectiveAmbientHom s q y * projectiveAmbientHom s q x
    simpa only [map_mul] using congrArg (projectiveAmbientHom s q) hc.eq
  have hpm := projective_root_maps_to_ambient s q (x * y) hp
  rw [map_mul] at hpm
  have ha := (CFSGOrthogonalDIndexProjectiveRootAdjacency.projective_root_product_adjacency_iff
    (q.Extension 2) s (relativeInclusion s q g) (relativeInclusion s q h) hneK).mp
      ⟨projectiveAmbientHom s q x, hxp, hxm,
        projectiveAmbientHom s q y, hyp, hym, hcm, hpm⟩
  have hnondisjoint : ¬Disjoint (conjugateRootPlane s q g) (conjugateRootPlane s q h) := by
    intro hd
    have hdK := (scalarSpan_disjoint_iff (s + 2) q _ _).mpr hd
    rw [hG, hH] at hdK
    have hz := congrArg
      (fun T : Submodule (q.Extension 2) (Index (s + 4) → q.Extension 2) =>
        Module.finrank (q.Extension 2) T) (disjoint_iff.mp hdK)
    dsimp only at hz
    rw [finrank_bot, ha.1] at hz
    omega
  refine ⟨CFSGTwoPlaneIntersectionPartition.inf_finrank_eq_one_of_not_disjoint _ _
    (conjugateRootPlane_finrank s q g) (conjugateRootPlane_finrank s q h) hne hnondisjoint, ?_⟩
  intro z hz
  obtain ⟨u, hu, v, hv, rfl⟩ := Submodule.mem_sup.mp hz
  have huK : u.val ∈ G := by
    rw [← hG]
    exact (fixed_mem_scalarSpan_iff (s + 2) q _ u).mpr hu
  have hvK : v.val ∈ H := by
    rw [← hH]
    exact (fixed_mem_scalarSpan_iff (s + 2) q _ v).mpr hv
  have huS : u.val ∈ G ⊔ H := (show G ≤ G ⊔ H from le_sup_left) huK
  have hvS : v.val ∈ G ⊔ H := (show H ≤ G ⊔ H from le_sup_right) hvK
  have hzK := ha.2 (u.val + v.val) ((G ⊔ H).add_mem huS hvS)
  apply Subtype.ext
  rw [fixedQuadraticForm_apply]
  exact hzK

end SymmetricSubgroupAsymptotics.CFSGTwistedDRootProductAdjacencyNecessity
