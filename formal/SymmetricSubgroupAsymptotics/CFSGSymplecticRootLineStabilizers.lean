import SymmetricSubgroupAsymptotics.CFSGSymplecticTransvectionLines

/-! For the actual natural isometries, root-line normalizers are
exactly projective-point stabilizers. Centralizing a nonidentity root
element fixes its vector up to a scalar whose square is one. This is
concrete recognition inside the natural action; no assertion about
arbitrary abstract automorphisms is substituted. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGSymplecticTransvectionGeometry
open CFSGSymplecticSerreMatrices
variable {K : Type} [Field K]

theorem natural_transvection_conjugation (r : ℕ)
    (A : (Index r → K) ≃ₗ[K] (Index r → K))
    (hA : ∀ x y, pairing r (A x) (A y) = pairing r x y)
    (v : Index r → K) (a : K) :
    A * transvection r v a * A⁻¹ = transvection r (A v) a := by
  apply LinearEquiv.ext
  intro x
  change A (transvection r v a (A.symm x)) = transvection r (A v) a x
  have hp := hA v (A.symm x)
  rw [A.apply_symm_apply] at hp
  simp only [transvection_apply, map_add, map_smul, A.apply_symm_apply]
  rw [← hp]

theorem naturalRootLine_map_conj (r : ℕ)
    (A : (Index r → K) ≃ₗ[K] (Index r → K))
    (hA : ∀ x y, pairing r (A x) (A y) = pairing r x y) (v : Index r → K) :
    (naturalRootLine r v).map (MulAut.conj A).toMonoidHom = naturalRootLine r (A v) := by
  ext T
  constructor
  · rintro ⟨S, ⟨a, rfl⟩, hT⟩
    refine ⟨a, ?_⟩
    change transvection r (A v) a.toAdd = T
    change A * transvection r v a.toAdd * A⁻¹ = T at hT
    exact (natural_transvection_conjugation r A hA v a.toAdd).symm.trans hT
  · rintro ⟨a, rfl⟩
    refine ⟨transvection r v a.toAdd, ⟨a, rfl⟩, ?_⟩
    exact natural_transvection_conjugation r A hA v a.toAdd

theorem naturalRootLine_normalizer_iff (r : ℕ)
    (A : (Index r → K) ≃ₗ[K] (Index r → K))
    (hA : ∀ x y, pairing r (A x) (A y) = pairing r x y)
    (v : Index r → K) (hv : v ≠ 0) :
    (naturalRootLine r v).map (MulAut.conj A).toMonoidHom = naturalRootLine r v ↔
      ∃ c : K, c ≠ 0 ∧ A v = c • v := by
  have hAv : A v ≠ 0 := by
    intro hz
    apply hv
    exact A.injective (hz.trans (map_zero A).symm)
  rw [naturalRootLine_map_conj r A hA v]
  exact naturalRootLine_eq_iff r (A v) v hAv

theorem natural_transvection_centralizer_iff (r : ℕ)
    (A : (Index r → K) ≃ₗ[K] (Index r → K))
    (hA : ∀ x y, pairing r (A x) (A y) = pairing r x y)
    (v : Index r → K) (hv : v ≠ 0) :
    Commute A (transvection r v 1) ↔
      ∃ c : K, c ≠ 0 ∧ A v = c • v ∧ c ^ 2 = 1 := by
  have hAv : A v ≠ 0 := by
    intro hz
    apply hv
    exact A.injective (hz.trans (map_zero A).symm)
  constructor
  · intro hc
    have hj : A * transvection r v 1 * A⁻¹ = transvection r v 1 := by
      rw [hc.eq]
      simp only [mul_assoc, mul_inv_cancel, mul_one]
    have ht : transvection r (A v) 1 = transvection r v 1 :=
      (natural_transvection_conjugation r A hA v 1).symm.trans hj
    obtain ⟨c, hc, hcv, hp⟩ := (transvection_eq_iff r (A v) v 1 1 hAv hv one_ne_zero).mp ht
    exact ⟨c, hc, hcv, by simpa only [one_mul] using hp.symm⟩
  · rintro ⟨c, _, hcv, hp⟩
    have hj : A * transvection r v 1 * A⁻¹ = transvection r v 1 := by
      rw [natural_transvection_conjugation r A hA v 1, hcv, transvection_smul, hp, mul_one]
    change A * transvection r v 1 = transvection r v 1 * A
    calc
      _ = (A * transvection r v 1 * A⁻¹) * A := by
        simp only [mul_assoc, inv_mul_cancel, mul_one]
      _ = _ := by rw [hj]

end SymmetricSubgroupAsymptotics.CFSGSymplecticTransvectionGeometry
