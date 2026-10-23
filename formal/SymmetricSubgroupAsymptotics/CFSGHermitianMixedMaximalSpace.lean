import SymmetricSubgroupAsymptotics.CFSGHermitianMixedLinearRatio
import SymmetricSubgroupAsymptotics.CFSGHermitianMaximalExchange

/-! The mixed-ray ratio is obtained from an actual maximal extension of
the perpendicular hyperplane and the outside singular vector. All
linear representatives are those on the same literal singular spaces. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGHermitianOrthogonalSpan
open CFSGTwistedAUnitaryParameters
variable {K I : Type*} [Field K] [Fintype I]
variable (sigma : K ≃+* K) (H : Matrix I I K)

def restrictedHermitianKernel (S : IsotropicSpace sigma H) (y : I → K) :
    Submodule K (I → K) := S.val ⊓ (pairRightLinear sigma H y).ker

theorem restrictedHermitianKernel_nonzero (S : IsotropicSpace sigma H)
    (hd : 3 ≤ Module.finrank K S.val) (y : I → K) :
    restrictedHermitianKernel sigma H S y ≠ ⊥ := by
  apply Submodule.one_le_finrank_iff.mp
  have hn := finrank_inf_ker_add_one_ge S.val (pairRightLinear sigma H y)
  change Module.finrank K S.val ≤ Module.finrank K (restrictedHermitianKernel sigma H S y) + 1 at hn
  omega

theorem exists_hermitian_mixed_ray_ratio
    (hswap : ∀ x y, hermitianPair sigma H x y = 0 ↔ hermitianPair sigma H y x = 0)
    (f : Equiv.Perm (SingularPoint sigma H)) (S : IsotropicSpace sigma H)
    (hd : 3 ≤ Module.finrank K S.val)
    (hlinear : ∀ M : MaximalSpace sigma H,
      Nonempty (SemilinearPiece sigma H f ⟨M.val, M.property.1⟩ (RingEquiv.refl K)))
    (y : I → K) (hy : hermitianPair sigma H y y = 0) (hyn : y ∉ S.val)
    (hfixS : ∀ P : SingularPoint sigma H, P.val ≤ S.val → f P = P)
    (hfixY : ∀ P : SingularPoint sigma H, P.val ≤ K ∙ y → f P = P) :
    ∃ t : K, t ≠ 0 ∧ ∀ (x : I → K) (hx : x ∈ restrictedHermitianKernel sigma H S y)
      (hxy0 : x + y ≠ 0) (hz : hermitianPair sigma H (x + y) (x + y) = 0),
      (f (singularRay sigma H (x + y) hxy0 hz)).val = K ∙ (x + t • y) := by
  let C := restrictedHermitianKernel sigma H S y
  have hCS : C ≤ S.val := inf_le_left
  have hyC : ∀ x ∈ C, hermitianPair sigma H y x = 0 := fun _ hx => hx.2
  have hCy : ∀ x ∈ C, hermitianPair sigma H x y = 0 := fun x hx => (hswap y x).mp (hyC x hx)
  have hC : Orthogonal sigma H C C := fun x hx z hz => S.property x (hCS hx) z (hCS hz)
  have hjoin : Orthogonal sigma H (C ⊔ K ∙ y) (C ⊔ K ∙ y) := by
    rw [orthogonal_sup_left_iff, orthogonal_sup_right_iff, orthogonal_sup_right_iff]
    exact ⟨⟨hC, (orthogonal_span_right_iff sigma H C y).mpr hCy⟩,
      (orthogonal_span_left_iff sigma H C y).mpr hyC, span_orthogonal_self sigma H y hy⟩
  obtain ⟨M, hJM, hM⟩ := exists_maximalIsotropic_ge sigma H _ hjoin
  obtain ⟨F⟩ := hlinear ⟨M, hM⟩
  have hCM : C ≤ M := (show C ≤ C ⊔ K ∙ y from le_sup_left).trans hJM
  have hyM : y ∈ M := hJM ((show K ∙ y ≤ C ⊔ K ∙ y from le_sup_right)
    (Submodule.mem_span_singleton_self y))
  have hy0 : y ≠ 0 := fun h => hyn (h ▸ S.val.zero_mem)
  obtain ⟨t, ht, hr⟩ := hermitian_mixed_piece_ray_ratio sigma H f ⟨M, hM.1⟩ F C hCM
    (restrictedHermitianKernel_nonzero sigma H S hd y) y hyM hy0
    (fun P hP => hfixS P (hP.trans hCS)) hfixY
  exact ⟨t, ht, fun x hx hxy0 _ => hr x hx hxy0⟩

end SymmetricSubgroupAsymptotics.CFSGHermitianOrthogonalSpan
