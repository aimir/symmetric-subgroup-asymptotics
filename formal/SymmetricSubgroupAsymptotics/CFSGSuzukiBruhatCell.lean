import SymmetricSubgroupAsymptotics.CFSGSuzukiBruhatArray
import SymmetricSubgroupAsymptotics.CFSGSuzukiWeylTorus
import SymmetricSubgroupAsymptotics.CFSGSuzukiUnipotentProduct

/-! Literal Suzuki inputs for a rank-one Bruhat closure argument. The
Borel, unipotent, torus and Weyl element are the SAME actual objects
used in the original matrix-model proofs. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGSuzukiBruhat
open CFSGSuzukiUnipotent CFSGSuzukiTorus CFSGSuzukiFieldParameters

theorem weyl_normalizes_torus (m : ℕ) :
    ∀ t∈(normalizedTorusHom m).range,
      weylElement m*t*(weylElement m)⁻¹∈(normalizedTorusHom m).range := by
  rintro t ⟨c,rfl⟩
  change weylElement m*normalizedTorusElement m c*(weylElement m)⁻¹∈
    (normalizedTorusHom m).range
  rw [weyl_normalizedTorus_conjugation]
  exact ⟨c⁻¹,rfl⟩

/-- Every conjugated original U element lies in the identity cell or
in the original B-times-W-times-U cell. -/
theorem weyl_unipotent_cell (m : ℕ) (u : CFSGSuzukiTorus.Ambient m)
    (hu : u∈unipotentSubgroup m) :
    weylElement m*u*weylElement m∈borelEnvelope m ∨
      ∃ b∈borelEnvelope m,∃ v∈unipotentSubgroup m,
        weylElement m*u*weylElement m=b*weylElement m*v := by
  obtain ⟨a,b,rfl⟩ := hu
  rcases weyl_unipotent_weyl_normal_form m a b with he|⟨x,y,c,z,w,he⟩
  · left
    rw [he]
    exact (borelEnvelope m).one_mem
  · right
    refine ⟨unipotentElement m x y*normalizedTorusElement m c,?_,
      unipotentElement m z w,⟨z,w,rfl⟩,he⟩
    exact (borelEnvelope m).mul_mem
      (unipotentSubgroup_le_borelEnvelope m ⟨x,y,rfl⟩)
      (normalizedTorus_mem_borelEnvelope m c)

end SymmetricSubgroupAsymptotics.CFSGSuzukiBruhat
