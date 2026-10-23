import SymmetricSubgroupAsymptotics.CFSGHermitianFixedLinearRestriction
import SymmetricSubgroupAsymptotics.CFSGHermitianSingularRay

/-! A linear representative fixes a hyperplane and a transverse point
with one common nonzero mixed-ray ratio. This keeps literal vector
coefficients and will be used when gluing the maximal-space pieces. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGHermitianOrthogonalSpan
variable {K I : Type*} [Field K] [Fintype I]
variable (sigma : K ≃+* K) (H : Matrix I I K)

theorem hermitian_mixed_piece_ray_ratio
    (f : Equiv.Perm (SingularPoint sigma H)) (S : IsotropicSpace sigma H)
    (F : SemilinearPiece sigma H f S (RingEquiv.refl K))
    (T : Submodule K (I → K)) (hTS : T ≤ S.val) (hT : T ≠ ⊥)
    (y : I → K) (hy : y ∈ S.val) (hy0 : y ≠ 0)
    (hfixT : ∀ P : SingularPoint sigma H, P.val ≤ T → f P = P)
    (hfixY : ∀ P : SingularPoint sigma H, P.val ≤ K ∙ y → f P = P) :
    ∃ t : K, t ≠ 0 ∧ ∀ (x : I → K) (hx : x ∈ T) (hxy0 : x + y ≠ 0),
      (f (singularRay sigma H (x + y) hxy0
        (S.property (x + y) (S.val.add_mem (hTS hx) hy)
          (x + y) (S.val.add_mem (hTS hx) hy)))).val = K ∙ (x + t • y) := by
  have hYS : K ∙ y ≤ S.val := (Submodule.span_singleton_le_iff_mem _ _).mpr hy
  have hY : (K ∙ y : Submodule K (I → K)) ≠ ⊥ := by
    intro h
    have hm : y ∈ (⊥ : Submodule K (I → K)) := h ▸ Submodule.mem_span_singleton_self y
    exact hy0 hm
  obtain ⟨a, ha, haF⟩ := hermitian_fixed_restriction_scalar_nonzero sigma H f S F T hTS hT hfixT
  obtain ⟨b, hb, hbF⟩ := hermitian_fixed_restriction_scalar_nonzero sigma H f S F (K ∙ y) hYS hY hfixY
  refine ⟨b / a, div_ne_zero hb ha, ?_⟩
  intro x hx hxy0
  have hxS := hTS hx
  have hxyS := S.val.add_mem hxS hy
  have hxyS0 : (⟨x + y, hxyS⟩ : S.val) ≠ 0 := fun h =>
    hxy0 (congrArg (fun z : S.val => z.val) h)
  have hsum : F.map ⟨x + y, hxyS⟩ = a • x + b • y := by
    have hh := F.map.map_add (⟨x, hxS⟩ : S.val) (⟨y, hy⟩ : S.val)
    change F.map ⟨x + y, hxyS⟩ = F.map ⟨x, hxS⟩ + F.map ⟨y, hy⟩ at hh
    rw [haF ⟨x, hx⟩, hbF ⟨y, Submodule.mem_span_singleton_self y⟩] at hh
    exact hh
  have hscale : a • x + b • y = a • (x + (b / a) • y) := by
    rw [smul_add, smul_smul]
    congr 1
    congr 1
    field_simp
  have hp := F.ray ⟨x + y, hxyS⟩ hxyS0
  rw [← singularRay_eq_projectiveInside sigma H S ⟨x + y, hxyS⟩ hxyS0] at hp
  rw [← hp, hsum, hscale]
  exact Submodule.span_singleton_smul_eq (isUnit_iff_ne_zero.mpr ha) _

end SymmetricSubgroupAsymptotics.CFSGHermitianOrthogonalSpan
