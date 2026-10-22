import SymmetricSubgroupAsymptotics.CFSGOrthogonalBLinearPolarIsometry
import SymmetricSubgroupAsymptotics.CFSGOrthogonalBFieldNormalization

/-! The actual original B point/plane automorphism is realized by ONE
coordinate field map followed by a literal special isometry. Global
field coherence and whole-space linear realization are proved above;
no independent polar-automorphism classification is assumed. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalBSemilinearPolarIsometry
open CFSGOrthogonalBSerreMatrices CFSGOrthogonalBSpecialFormGroup CFSGPolarSubspacePoints
open CFSGSingularPlaneTriangle CFSGOrthogonalBFieldGeometry CFSGOrthogonalBGlobalField
open CFSGOrthogonalBPlaneFamilyAction
variable (K : Type) [Field K] [Finite K]

theorem exists_field_special_decomposition (p : ℕ) [Fact p.Prime] [CharP K p]
    (h2 : (2 : K)≠0) (s : ℕ)
    (f : Points (gram K (s+3)).toBilin'≃Points (gram K (s+3)).toBilin')
    (l : Planes (gram K (s+3)).toBilin'≃Planes (gram K (s+3)).toBilin')
    (hinc : ∀P L,(f P).val≤(l L).val ↔ P.val≤L.val)
    (horth : ∀P Q,ZeroOn (gram K (s+3)).toBilin' (f P).val (f Q).val ↔
      ZeroOn (gram K (s+3)).toBilin' P.val Q.val) :
    ∃(σ : K≃+*K) (g : specialFormUnits K (s+3)),
      normalizedPoints (s+3) f σ=CFSGOrthogonalBSpecialGeometry.point K (s+3) g := by
  obtain ⟨σ,hlinear⟩ := exists_linear_normalization K h2 s f l hinc horth
  obtain ⟨g,hg⟩ := CFSGOrthogonalBLinearPolarIsometry.exists_special_isometry_of_linear_pieces
    K p h2 s (normalizedPoints (s+3) f σ) (normalizedPlanes (s+3) l σ)
    (normalized_incidence (s+3) f l hinc σ) (normalized_orthogonality (s+3) f horth σ) hlinear
  exact ⟨σ,g,hg⟩

theorem original_field_special_decomposition (p : ℕ) [Fact p.Prime] [CharP K p]
    (h2 : (2 : K)≠0) (s : ℕ) (F : MulAut (elementaryProjective K (s+3))) :
    ∃(σ : K≃+*K) (g : specialFormUnits K (s+3)),
      normalizedPoints (s+3) (originalPointAction p h2 s F).val σ=
        CFSGOrthogonalBSpecialGeometry.point K (s+3) g :=
  exists_field_special_decomposition K p h2 s (originalPointAction p h2 s F).val
    (singularActionHom p h2 s F) (originalPointAction_incidence p h2 s F)
    (originalPointAction_preserves_orthogonal p h2 s F)

end SymmetricSubgroupAsymptotics.CFSGOrthogonalBSemilinearPolarIsometry
