import SymmetricSubgroupAsymptotics.CFSGTrialityGeckMiddleFixedPairingValues
import SymmetricSubgroupAsymptotics.ScalarExtensionSpanningPairing

/-! The actual fixed middle quotient carries a nondegenerate alternating
pairing over its literal fixed field. Its nondegeneracy is descended from
the original coefficient space using the proved full extension-field span,
without averaging by the cubic degree. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGTrialityGeckMiddleFixedScalarPairing

open CFSGTrialityGeckMiddleFirstLayer CFSGTrialityGeckMiddleCubeSpanActions
open CFSGTrialityMiddleFixedTensorSpan CFSGTrialityGeckMiddleFixedTensorImage
open CFSGTrialityGeckMiddleFixedPairingValues CFSGTrialityGeckMiddleScalarPairing

def fixedPairing (q : CFSG.PrimePower) : fullEnvelope q →ₗ[F q] fullEnvelope q →ₗ[F q] F q where
  toFun c :=
    { toFun := fun d =>
        ⟨cubePairing (K q) (fixedCubeEmbedding q c) (fixedCubeEmbedding q d), pairing_fixed_field q c d⟩
      map_add' := by
        intro d e
        apply Subtype.ext
        change cubePairing (K q) (fixedCubeEmbedding q c) (fixedCubeEmbedding q (d+e)) =
          cubePairing (K q) (fixedCubeEmbedding q c) (fixedCubeEmbedding q d) +
            cubePairing (K q) (fixedCubeEmbedding q c) (fixedCubeEmbedding q e)
        rw [map_add, map_add]
      map_smul' := by
        intro a d
        apply Subtype.ext
        change cubePairing (K q) (fixedCubeEmbedding q c) (fixedCubeEmbedding q (a • d)) =
          a.val * cubePairing (K q) (fixedCubeEmbedding q c) (fixedCubeEmbedding q d)
        rw [map_smul]
        change cubePairing (K q) (fixedCubeEmbedding q c)
          ((a.val : K q) • fixedCubeEmbedding q d) = _
        rw [map_smul]
        rfl }
  map_add' := by
    intro c d
    ext e
    change cubePairing (K q) (fixedCubeEmbedding q (c+d)) (fixedCubeEmbedding q e) =
      cubePairing (K q) (fixedCubeEmbedding q c) (fixedCubeEmbedding q e) +
        cubePairing (K q) (fixedCubeEmbedding q d) (fixedCubeEmbedding q e)
    simp only [map_add, LinearMap.add_apply]
  map_smul' := by
    intro a c
    ext d
    change cubePairing (K q) (fixedCubeEmbedding q (a • c)) (fixedCubeEmbedding q d) =
      a.val * cubePairing (K q) (fixedCubeEmbedding q c) (fixedCubeEmbedding q d)
    rw [map_smul]
    change cubePairing (K q) ((a.val : K q) • fixedCubeEmbedding q c)
      (fixedCubeEmbedding q d) = _
    rw [map_smul]
    rfl

theorem fixedPairing_val (q : CFSG.PrimePower) (c d : fullEnvelope q) :
    (fixedPairing q c d).val = cubePairing (K q) (fixedCubeEmbedding q c) (fixedCubeEmbedding q d) := rfl

theorem fixedCubeEmbedding_span (q : CFSG.PrimePower) :
    Submodule.span (K q) (Set.range (fixedCubeEmbedding q)) = ⊤ := by
  let S := Submodule.span (K q) (Set.range (fixedCubeEmbedding q))
  have hmap : S.map (cubeSpan (K q)).subtype = cubeSpan (K q) := by
    have hr : (cubeSpan (K q)).subtype '' Set.range (fixedCubeEmbedding q) =
        Set.range (fixedTensorEmbedding q) := by
      ext x
      constructor
      · rintro ⟨y,⟨c,rfl⟩,rfl⟩
        exact ⟨c,rfl⟩
      · rintro ⟨c,rfl⟩
        exact ⟨fixedCubeEmbedding q c,⟨c,rfl⟩,rfl⟩
    rw [Submodule.map_span,hr]
    exact fixedTensorEmbedding_span q
  apply top_unique
  intro x _
  have hx : x.val ∈ S.map (cubeSpan (K q)).subtype := by rw [hmap]; exact x.property
  obtain ⟨y, hy, hey⟩ := hx
  have hxy : y = x := Subtype.ext hey
  exact hxy ▸ hy

theorem fixedPairing_alternating (q : CFSG.PrimePower) (c : fullEnvelope q) :
    fixedPairing q c c = 0 := by
  apply Subtype.ext
  exact cubePairing_alternating (K q) (fixedCubeEmbedding q c)

theorem fixedPairing_separating (q : CFSG.PrimePower) (c : fullEnvelope q)
    (hc : ∀ d, fixedPairing q c d = 0) : c = 0 :=
  ScalarExtensionSpanningPairing.separating_of_spanning_image (fixedPairing q) (cubePairing (K q))
    (fixedCubeEmbedding q) (fixedCubeEmbedding_injective q) (fixedCubeEmbedding_span q)
    (fun _ _ => rfl) (cubePairing_separating (K q)) c hc

theorem fixedPairing_full (q : CFSG.PrimePower) (c : fullEnvelope q) (hc : c ≠ 0) :
    Function.Surjective (fixedPairing q c) :=
  ScalarExtensionSpanningPairing.surjective_of_spanning_image (fixedPairing q) (cubePairing (K q))
    (fixedCubeEmbedding q) (fixedCubeEmbedding_injective q) (fixedCubeEmbedding_span q)
    (fun _ _ => rfl) (cubePairing_separating (K q)) c hc

end SymmetricSubgroupAsymptotics.CFSGTrialityGeckMiddleFixedScalarPairing
