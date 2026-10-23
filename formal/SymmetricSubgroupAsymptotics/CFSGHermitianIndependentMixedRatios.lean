import SymmetricSubgroupAsymptotics.CFSGHermitianRectangleRatio
import SymmetricSubgroupAsymptotics.CFSGHermitianIsotropicRectangle
import SymmetricSubgroupAsymptotics.CFSGHermitianRankTwoMixedSpace

/-! Mixed-ray ratios agree on any two independent directions of an
opposed plane. The isotropic rectangle and its actual maximal extension
are constructed from the original form. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGHermitianOrthogonalSpan
open CFSGTwistedAUnitaryParameters
variable {K I : Type*} [Field K] [Fintype I]
variable (sigma : K ≃+* K) (H : Matrix I I K)

private theorem maximal_contains_orthogonal_pair
    (hswap : ∀ x y, hermitianPair sigma H x y = 0 ↔ hermitianPair sigma H y x = 0)
    (z w : I → K) (hz : hermitianPair sigma H z z = 0)
    (hw : hermitianPair sigma H w w = 0) (hzw : hermitianPair sigma H z w = 0) :
    ∃ M : MaximalSpace sigma H, z ∈ M.val ∧ w ∈ M.val := by
  have hzw' : Orthogonal sigma H (K ∙ z) (K ∙ w) := by
    apply (orthogonal_span_left_iff sigma H _ z).mpr
    intro v hv
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hv
    have hh := hermitianPair_smul sigma H 1 a z w
    simpa only [one_smul, map_one, one_mul, hzw, mul_zero] using hh
  have hwz' : Orthogonal sigma H (K ∙ w) (K ∙ z) := by
    intro v hv u hu
    exact (hswap u v).mp (hzw' u hu v hv)
  have hjoin : Orthogonal sigma H ((K ∙ z) ⊔ K ∙ w) ((K ∙ z) ⊔ K ∙ w) := by
    rw [orthogonal_sup_left_iff, orthogonal_sup_right_iff, orthogonal_sup_right_iff]
    exact ⟨⟨span_orthogonal_self sigma H z hz, hzw'⟩,
      hwz', span_orthogonal_self sigma H w hw⟩
  obtain ⟨M, hle, hM⟩ := exists_maximalIsotropic_ge sigma H _ hjoin
  exact ⟨⟨M, hM⟩,
    hle ((show K ∙ z ≤ (K ∙ z) ⊔ K ∙ w from le_sup_left) (Submodule.mem_span_singleton_self z)),
    hle ((show K ∙ w ≤ (K ∙ z) ⊔ K ∙ w from le_sup_right) (Submodule.mem_span_singleton_self w))⟩

private theorem piece_image_nonzero_scalar
    (f : Equiv.Perm (SingularPoint sigma H)) (M : IsotropicSpace sigma H)
    (F : SemilinearPiece sigma H f M (RingEquiv.refl K))
    (z v : I → K) (hzM : z ∈ M.val) (hz0 : z ≠ 0)
    (hz : hermitianPair sigma H z z = 0)
    (he : (f (singularRay sigma H z hz0 hz)).val = K ∙ v) :
    ∃ a : K, a ≠ 0 ∧ F.map ⟨z, hzM⟩ = a • v := by
  have hzM0 : (⟨z, hzM⟩ : M.val) ≠ 0 := fun h => hz0 (congrArg Subtype.val h)
  have hF0 : F.map ⟨z, hzM⟩ ≠ 0 := by
    intro h
    exact hzM0 (F.injective (h.trans F.map.map_zero.symm))
  have hp := F.ray ⟨z, hzM⟩ hzM0
  rw [← singularRay_eq_projectiveInside sigma H M ⟨z, hzM⟩ hzM0] at hp
  have hm : F.map ⟨z, hzM⟩ ∈ K ∙ v :=
    (hp.trans he) ▸ Submodule.mem_span_singleton_self (F.map ⟨z, hzM⟩)
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hm
  refine ⟨a, ?_, ha.symm⟩
  intro h
  exact hF0 (ha.symm.trans (by rw [h, zero_smul]))

private theorem disjoint_sum_nonzero
    (P Z : Submodule K (I → K)) (hdis : Disjoint P Z)
    (x y : I → K) (hx : x ∈ P) (hy : y ∈ Z) (hx0 : x ≠ 0) : x + y ≠ 0 := by
  intro h
  have hxZ : x ∈ Z := by
    rw [add_eq_zero_iff_eq_neg.mp h]
    exact Z.neg_mem hy
  exact hx0 ((Submodule.disjoint_def.mp hdis) x hx hxZ)

theorem hermitian_mixed_ratios_eq_of_independent
    (eps : K) (heps : eps ≠ 0)
    (hflip : ∀ v w, hermitianPair sigma H v w = eps * sigma (hermitianPair sigma H w v))
    (hswap : ∀ x y, hermitianPair sigma H x y = 0 ↔ hermitianPair sigma H y x = 0)
    (f : Equiv.Perm (SingularPoint sigma H)) (hf : PreservesOrthogonality sigma H f)
    (P Z : IsotropicSpace sigma H) (hdis : Disjoint P.val Z.val)
    (hdP : Module.finrank K P.val = 2)
    (hNDp : ∀ x ∈ P.val, (∀ y ∈ Z.val, hermitianPair sigma H x y = 0) → x = 0)
    (hNDz : ∀ y ∈ Z.val, (∀ x ∈ P.val, hermitianPair sigma H y x = 0) → y = 0)
    (hlinear : ∀ M : MaximalSpace sigma H,
      Nonempty (SemilinearPiece sigma H f ⟨M.val, M.property.1⟩ (RingEquiv.refl K)))
    (hfixP : ∀ R : SingularPoint sigma H, R.val ≤ P.val → f R = R)
    (hfixZ : ∀ R : SingularPoint sigma H, R.val ≤ Z.val → f R = R)
    (y : Fin 2 → I → K) (hspan : Submodule.span K (Set.range y) = Z.val)
    (hy : LinearIndependent K y) (t u : K)
    (ht : ∀ (x : I → K) (hx : x ∈ restrictedHermitianKernel sigma H P (y 0))
      (hz0 : x + y 0 ≠ 0) (hz : hermitianPair sigma H (x + y 0) (x + y 0) = 0),
      (f (singularRay sigma H (x + y 0) hz0 hz)).val = K ∙ (x + t • y 0))
    (hu : ∀ (x : I → K) (hx : x ∈ restrictedHermitianKernel sigma H P (y 1))
      (hz0 : x + y 1 ≠ 0) (hz : hermitianPair sigma H (x + y 1) (x + y 1) = 0),
      (f (singularRay sigma H (x + y 1) hz0 hz)).val = K ∙ (x + u • y 1)) : t = u := by
  have hND : ∀ x ∈ P.val, (∀ z ∈ Z.val, hermitianPair sigma H z x = 0) → x = 0 := by
    intro x hx hz
    exact hNDp x hx (fun z hzZ => (hswap z x).mp (hz z hzZ))
  obtain ⟨x₁, hx₁, x₂, hx₂, hx, h10, h21, hz₁, hz₂, hz₁₂⟩ :=
    exists_hermitian_isotropic_rectangle sigma H eps heps hflip P Z hdP y hspan hND
  have hyZ (j : Fin 2) : y j ∈ Z.val := by
    rw [← hspan]
    exact Submodule.subset_span ⟨j, rfl⟩
  have hx₁0 : x₁ ≠ 0 := hx.ne_zero 0
  have hx₂0 : x₂ ≠ 0 := hx.ne_zero 1
  have hs₁ : x₁ + y 0 ≠ 0 := disjoint_sum_nonzero P.val Z.val hdis x₁ (y 0) hx₁ (hyZ 0) hx₁0
  have hs₂ : x₂ + y 1 ≠ 0 := disjoint_sum_nonzero P.val Z.val hdis x₂ (y 1) hx₂ (hyZ 1) hx₂0
  obtain ⟨M, hm₁, hm₂⟩ := maximal_contains_orthogonal_pair sigma H hswap
    (x₁ + y 0) (x₂ + y 1) hz₁ hz₂ hz₁₂
  obtain ⟨F⟩ := hlinear M
  obtain ⟨a, ha, he₁⟩ := piece_image_nonzero_scalar sigma H f ⟨M.val, M.property.1⟩ F
    (x₁ + y 0) (x₁ + t • y 0) hm₁ hs₁ hz₁ (ht x₁ ⟨hx₁, h10⟩ hs₁ hz₁)
  obtain ⟨b, _, he₂⟩ := piece_image_nonzero_scalar sigma H f ⟨M.val, M.property.1⟩ F
    (x₂ + y 1) (x₂ + u • y 1) hm₂ hs₂ hz₂ (hu x₂ ⟨hx₂, h21⟩ hs₂ hz₂)
  have hy' : LinearIndependent K ![y 0, y 1] := by
    convert hy using 1
    ext j
    fin_cases j <;> rfl
  exact hermitian_rectangle_ratio_eq sigma H f hf P Z hdis hNDp hNDz hfixP hfixZ
    ⟨M.val, M.property.1⟩ F x₁ x₂ (y 0) (y 1) hx₁ hx₂ (hyZ 0) (hyZ 1) hx hy'
    hm₁ hm₂ a b t u ha he₁ he₂

end SymmetricSubgroupAsymptotics.CFSGHermitianOrthogonalSpan
