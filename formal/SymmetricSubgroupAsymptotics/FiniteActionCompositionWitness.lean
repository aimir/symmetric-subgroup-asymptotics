import SymmetricSubgroupAsymptotics.FiniteCompositionWitness
import SymmetricSubgroupAsymptotics.FaithfulFiniteActionImage

/-! Install a verified finite composition witness in an original faithful
action. The point labelling and equality with the literal permutation
image are explicit. Chosen chief series are pulled back by the actual
ambient equivalence, so the result applies to primitive inputs without
assuming primitivity, catalogue coverage, or classification here. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics

variable {A Ω : Type} [Group A] [MulAction A Ω] [FaithfulSMul A Ω]
variable {n : ℕ} (e : Ω ≃ Fin n)

/-- Recognition is equality with the image of the original labelled
action, not equality of orders or an abstract catalogue name. -/
def faithfulCompositionImageEquiv (P : Subgroup (Equiv.Perm (Fin n)))
    (hImage : labelledActionImage (A := A) e = P) : A ≃* P :=
  (faithfulLabelledActionEquiv e).trans (MulEquiv.subgroupCongr hImage)

@[simp] theorem faithfulCompositionImageEquiv_coe
    (P : Subgroup (Equiv.Perm (Fin n)))
    (hImage : labelledActionImage (A := A) e = P) (a : A) :
    (faithfulCompositionImageEquiv e P hImage a : Equiv.Perm (Fin n)) =
      labelledActionHom e a := rfl

/-- A concrete chosen series in the original group. Its subgroups are
literal inverse images under the original action's faithful equivalence. -/
def faithfulCompositionChiefSeries (P : Subgroup (Equiv.Perm (Fin n)))
    (hImage : labelledActionImage (A := A) e = P) : ActualChiefSeries A :=
  actualChiefSeriesComap (faithfulCompositionImageEquiv e P hImage) (actualChiefSeries P)

theorem faithfulCompositionChiefSeries_weight_le
    (P : Subgroup (Equiv.Perm (Fin n)))
    (hImage : labelledActionImage (A := A) e = P)
    (C : FiniteCompositionOrderCertificate P) :
    actualChiefSeriesTernaryWeight (faithfulCompositionChiefSeries e P hImage) ≤
      C.count 3 := by
  change actualChiefSeriesTernaryWeight
    (actualChiefSeriesComap (faithfulCompositionImageEquiv e P hImage)
      (actualChiefSeries P)) ≤ C.count 3
  rw [actualChiefSeriesComap_weight]
  exact C.chiefWeight_le (actualChiefSeries P)

/-- The certificate also bounds an independently chosen original chief
series; no special choice of series or invariant-count premise is needed. -/
theorem faithfulActionChiefWeight_le_composition_count
    (P : Subgroup (Equiv.Perm (Fin n)))
    (hImage : labelledActionImage (A := A) e = P)
    (C : FiniteCompositionOrderCertificate P) (c : ActualChiefSeries A) :
    actualChiefSeriesTernaryWeight c ≤ C.count 3 := by
  let E := faithfulCompositionImageEquiv e P hImage
  have h := C.chiefWeight_le (actualChiefSeriesComap E.symm c)
  rwa [actualChiefSeriesComap_weight] at h

/-- This is the per-original-action chosen-weight input used by primitive
induction. The finite count inequality is justified only after the actual
chain and image bindings have been supplied. -/
theorem faithfulAction_exists_chiefSeries_le_of_composition_certificate
    (P : Subgroup (Equiv.Perm (Fin n)))
    (hImage : labelledActionImage (A := A) e = P)
    (C : FiniteCompositionOrderCertificate P) (b : ℕ) (hb : C.count 3 ≤ b) :
    ∃ c : ActualChiefSeries A, actualChiefSeriesTernaryWeight c ≤ b :=
  ⟨faithfulCompositionChiefSeries e P hImage,
    (faithfulCompositionChiefSeries_weight_le e P hImage C).trans hb⟩

/-- A family of checked rows is usable only with explicit recognition of
the original labelled image. Finiteness of a menu is not a completeness
proof; the recognition witness is deliberately a separate hypothesis. -/
theorem faithfulActionChiefWeight_le_of_composition_family
    {ι : Type} (P : ι → Subgroup (Equiv.Perm (Fin n)))
    (C : ∀ i, FiniteCompositionOrderCertificate (P i))
    (hRecognize : ∃ i, labelledActionImage (A := A) e = P i)
    (b : ℕ) (hCount : ∀ i, (C i).count 3 ≤ b) (c : ActualChiefSeries A) :
    actualChiefSeriesTernaryWeight c ≤ b := by
  obtain ⟨i, hi⟩ := hRecognize
  exact (faithfulActionChiefWeight_le_composition_count e (P i) hi (C i) c).trans
    (hCount i)

theorem faithfulAction_exists_chiefSeries_le_of_composition_family
    {ι : Type} (P : ι → Subgroup (Equiv.Perm (Fin n)))
    (C : ∀ i, FiniteCompositionOrderCertificate (P i))
    (hRecognize : ∃ i, labelledActionImage (A := A) e = P i)
    (b : ℕ) (hCount : ∀ i, (C i).count 3 ≤ b) :
    ∃ c : ActualChiefSeries A, actualChiefSeriesTernaryWeight c ≤ b := by
  obtain ⟨i, hi⟩ := hRecognize
  exact faithfulAction_exists_chiefSeries_le_of_composition_certificate
    e (P i) hi (C i) b (hCount i)

end SymmetricSubgroupAsymptotics
