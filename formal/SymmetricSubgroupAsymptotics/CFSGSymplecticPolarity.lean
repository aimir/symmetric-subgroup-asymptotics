import SymmetricSubgroupAsymptotics.CFSGSymplecticProjectiveRootLift
import SymmetricSubgroupAsymptotics.CFSGProjectivizationLinearEquiv
import SymmetricSubgroupAsymptotics.CFSGProjectiveIncidenceCollineation

/-! The literal alternating pairing identifies natural vectors with
dual vectors. Thus every orthogonality-preserving point permutation
preserves ALL projective lines, by the already-proved incidence theorem.
This supplies concrete geometry without an abstract recognition premise. -/
set_option autoImplicit false
noncomputable section
open scoped LinearAlgebra.Projectivization
namespace SymmetricSubgroupAsymptotics.CFSGSymplecticPolarity
open Module CFSGSymplecticSerreMatrices CFSGSymplecticTransvectionGeometry
variable (K : Type) [Field K]

 def vectorDualEquiv (n : ℕ) :
    (Index n → K) ≃ₗ[K] Dual K (Index n → K) where
  toFun := pairingDual n
  invFun f := Sum.elim (fun i => f (Pi.single (Sum.inr i) 1))
    (fun i => -f (Pi.single (Sum.inl i) 1))
  left_inv v := by
    funext i
    cases i <;> simp [pairingDual, pairing_pos_basis, pairing_neg_basis]
  right_inv f := by
    apply (Pi.basisFun K (Index n)).ext
    intro i
    cases i <;> simp [pairingDual, pairing_pos_basis, pairing_neg_basis]
  map_add' v w := by
    apply LinearMap.ext
    intro x
    exact pairing_add_left n v w x
  map_smul' c v := by
    apply LinearMap.ext
    intro x
    exact pairing_smul_left n c v x

 abbrev Points (n : ℕ) := ℙ K (Index n → K)
 abbrev Hyperplanes (n : ℕ) := ℙ K (Dual K (Index n → K))

 def polarity (n : ℕ) : Points K n ≃ Hyperplanes K n :=
  CFSGProjectivizationLinearEquiv.map (vectorDualEquiv K n)

 def Orthogonal (n : ℕ) (p q : Points K n) : Prop := pairing n p.rep q.rep = 0

 theorem incident_polarity (n : ℕ) (p q : Points K n) :
    CFSGProjectiveIncidence.Incident q (polarity K n p) ↔ Orthogonal K n p q := by
  have hf : pairingDual n p.rep ≠ 0 := by
    intro hz
    apply p.rep_nonzero
    apply (vectorDualEquiv K n).injective
    simpa only [map_zero] using hz
  have he : polarity K n p = Projectivization.mk K (pairingDual n p.rep) hf := by
    conv_lhs => rw [← Projectivization.mk_rep p]
    exact CFSGProjectivizationLinearEquiv.map_mk (vectorDualEquiv K n) p.rep p.rep_nonzero
  rw [he, CFSGProjectiveIncidence.incident_mk_form]
  rfl

 theorem orthogonal_permutation_mem_collineation (n : ℕ)
    (e : Equiv.Perm (Points K n))
    (he : ∀ p q, Orthogonal K n (e p) (e q) ↔ Orthogonal K n p q) :
    e ∈ CFSGProjectiveFrameCoordinates.collineationGroup (F := K) (n := Index n) := by
  let d : Equiv.Perm (Hyperplanes K n) :=
    (polarity K n).symm.trans (e.trans (polarity K n))
  apply CFSGProjectiveIncidenceCollineation.point_permutation_mem_collineationGroup e d
  intro p h
  obtain ⟨q, rfl⟩ := (polarity K n).surjective h
  simp only [d, Equiv.trans_apply, Equiv.symm_apply_apply]
  change CFSGProjectiveIncidence.Incident (e p) (polarity K n (e q)) ↔
    CFSGProjectiveIncidence.Incident p (polarity K n q)
  rw [incident_polarity, incident_polarity]
  exact he q p

end SymmetricSubgroupAsymptotics.CFSGSymplecticPolarity
