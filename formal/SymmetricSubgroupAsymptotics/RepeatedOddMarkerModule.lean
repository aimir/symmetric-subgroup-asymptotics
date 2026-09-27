import SymmetricSubgroupAsymptotics.RepeatedOddMarkerKernel
import SymmetricSubgroupAsymptotics.OddMarkerTernaryChart
import SymmetricSubgroupAsymptotics.DiagonalIsotypeProjection
import Mathlib.Algebra.Module.ZMod

/-!
# Ternary coordinates for the actual repeated-marker joint kernel

The original subgroup H, all marker coordinates, and the whole exterior
are retained. The submodule consists precisely of ternary vectors whose
literal reconstructed original permutation tuple belongs to H. It is
multiplicatively equivalent to the actual joint sign/exterior kernel.

Conjugation by the same original H gives its actual diagonal sign action.
The resulting decomposition is indexed by distinct sign characters; equal
signs may still carry arbitrary correlations. Full coordinate projection
uses the original full S3 projection and the binary exterior hypothesis.
No product-kernel identity or physical counting statement is asserted.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics.RepeatedOddMarkerModule

open RepeatedOddMarkerKernel

variable {ι D : Type*} [Group D]

/-- Reconstruct every original A3 permutation and the identity exterior. -/
def reconstruction : Multiplicative (ι → ZMod 3) →* ((ι → OddMarkerGroup) × D) where
  toFun v := (fun i => (OddMarkerTernaryChart.chart
    (Multiplicative.ofAdd (v.toAdd i)) : OddMarkerGroup), 1)
  map_one' := by
    apply Prod.ext
    · funext i
      exact congrArg Subtype.val OddMarkerTernaryChart.chart.map_one
    · rfl
  map_mul' v w := by
    apply Prod.ext
    · funext i
      exact congrArg Subtype.val (OddMarkerTernaryChart.chart.map_mul
        (Multiplicative.ofAdd (v.toAdd i)) (Multiplicative.ofAdd (w.toAdd i)))
    · simp

theorem reconstruction_injective :
    Function.Injective (reconstruction (ι := ι) (D := D)) := by
  intro v w h
  apply Multiplicative.toAdd.injective
  funext i
  have hi := congrArg (fun x : (ι → OddMarkerGroup) × D => x.1 i) h
  have hc := OddMarkerTernaryChart.chart.injective (Subtype.ext hi)
  exact congrArg Multiplicative.toAdd hc

/-- Literal membership in H, expressed in ternary coordinates. -/
def kernelSubmodule (H : Subgroup ((ι → OddMarkerGroup) × D)) :
    Submodule (ZMod 3) (ι → ZMod 3) :=
  AddSubgroup.toZModSubmodule 3
    (Subgroup.toAddSubgroup' (H.comap reconstruction))

@[simp] theorem mem_kernelSubmodule (H : Subgroup ((ι → OddMarkerGroup) × D))
    (v : ι → ZMod 3) :
    v ∈ kernelSubmodule H ↔ reconstruction (Multiplicative.ofAdd v) ∈ H := Iff.rfl

theorem reconstruction_mem_jointKernel (H : Subgroup ((ι → OddMarkerGroup) × D))
    (v : ι → ZMod 3) (hv : v ∈ kernelSubmodule H) :
    reconstruction (Multiplicative.ofAdd v) ∈ jointKernel H := by
  apply (mem_jointKernel H _).mpr
  refine ⟨hv, ?_, rfl⟩
  intro i
  exact (OddMarkerTernaryChart.chart (Multiplicative.ofAdd (v i))).property

/-- The original group homomorphism, restricted to precisely its actual
joint kernel. This does not enlarge the submodule to a product. -/
def kernelMap (H : Subgroup ((ι → OddMarkerGroup) × D)) :
    Multiplicative (kernelSubmodule H) →* jointKernel H where
  toFun v := ⟨reconstruction (Multiplicative.ofAdd v.toAdd.1),
    reconstruction_mem_jointKernel H v.toAdd.1 v.toAdd.2⟩
  map_one' := Subtype.ext reconstruction.map_one
  map_mul' v w := Subtype.ext (reconstruction.map_mul
    (Multiplicative.ofAdd v.toAdd.1) (Multiplicative.ofAdd w.toAdd.1))

theorem kernelMap_injective (H : Subgroup ((ι → OddMarkerGroup) × D)) :
    Function.Injective (kernelMap H) := by
  intro v w h
  have he := reconstruction_injective (congrArg Subtype.val h)
  apply Multiplicative.toAdd.injective
  exact Subtype.ext (congrArg Multiplicative.toAdd he)

theorem kernelMap_surjective (H : Subgroup ((ι → OddMarkerGroup) × D)) :
    Function.Surjective (kernelMap H) := by
  intro x
  have hx := (mem_jointKernel H x.1).mp x.2
  let v : ι → ZMod 3 := fun i =>
    (OddMarkerTernaryChart.chart.symm ⟨x.1.1 i, hx.2.1 i⟩).toAdd
  have he : reconstruction (Multiplicative.ofAdd v) = x.1 := by
    apply Prod.ext
    · funext i
      exact congrArg Subtype.val
        (OddMarkerTernaryChart.chart.apply_symm_apply ⟨x.1.1 i, hx.2.1 i⟩)
    · exact hx.2.2.symm
  have hv : v ∈ kernelSubmodule H := by
    change reconstruction (Multiplicative.ofAdd v) ∈ H
    rw [he]
    exact hx.1
  exact ⟨Multiplicative.ofAdd ⟨v, hv⟩, Subtype.ext he⟩

/-- Explicit original reconstruction, rather than a dimension comparison. -/
def kernelEquiv (H : Subgroup ((ι → OddMarkerGroup) × D)) :
    Multiplicative (kernelSubmodule H) ≃* jointKernel H :=
  MulEquiv.ofBijective (kernelMap H) ⟨kernelMap_injective H, kernelMap_surjective H⟩

@[simp] theorem kernelEquiv_coe (H : Subgroup ((ι → OddMarkerGroup) × D))
    (v : Multiplicative (kernelSubmodule H)) :
    (kernelEquiv H v : (ι → OddMarkerGroup) × D) =
      reconstruction (Multiplicative.ofAdd v.toAdd.1) := rfl

/-- The sign character is a homomorphism on the same original H. -/
def signCharacter (H : Subgroup ((ι → OddMarkerGroup) × D)) (i : ι) :
    H →* Multiplicative (ZMod 2) :=
  oddMarkerSign.comp ((coordinate i).comp H.subtype)

def scalar (H : Subgroup ((ι → OddMarkerGroup) × D)) (i : ι) (h : H) : ZMod 3 :=
  OddMarkerTernaryChart.signScalar (signCharacter H i h)

theorem scalar_eq_iff_signCharacter_eq (H : Subgroup ((ι → OddMarkerGroup) × D))
    (i j : ι) : scalar H i = scalar H j ↔ signCharacter H i = signCharacter H j :=
  OddMarkerTernaryChart.signScalar_characters_eq_iff _ _

/-- Conjugation uses exactly the original tuple and the whole exterior. -/
theorem reconstruction_diagonal (H : Subgroup ((ι → OddMarkerGroup) × D))
    (h : H) (v : ι → ZMod 3) :
    reconstruction (Multiplicative.ofAdd
      (DiagonalIsotypeProjection.diagonalOperator (scalar H) h v)) =
      h.1 * reconstruction (Multiplicative.ofAdd v) * h.1⁻¹ := by
  apply Prod.ext
  · funext i
    exact (OddMarkerTernaryChart.chart_conjugate_coe (h.1.1 i)
      (Multiplicative.ofAdd (v i))).symm
  · change (1 : D) = h.1.2 * 1 * h.1.2⁻¹
    simp

/-- No normality of H in the ambient product is needed: the conjugator
belongs to H itself. No finiteness of H or of D is needed either. -/
theorem diagonal_mem (H : Subgroup ((ι → OddMarkerGroup) × D))
    (h : H) (v : ι → ZMod 3) (hv : v ∈ kernelSubmodule H) :
    DiagonalIsotypeProjection.diagonalOperator (scalar H) h v ∈ kernelSubmodule H := by
  change reconstruction (Multiplicative.ofAdd
    (DiagonalIsotypeProjection.diagonalOperator (scalar H) h v)) ∈ H
  rw [reconstruction_diagonal]
  exact H.mul_mem (H.mul_mem h.2 hv) (H.inv_mem h.2)

/-- Labels are the distinct original sign characters, with their domain H
unchanged. Equal-sign coordinates remain in a single correlated piece. -/
abbrev SignLabel (H : Subgroup ((ι → OddMarkerGroup) × D)) := Set.range (signCharacter H)

instance signLabelFintype [Fintype ι] (H : Subgroup ((ι → OddMarkerGroup) × D)) :
    Fintype (SignLabel H) := Fintype.ofFinite _

def scalarLabel (H : Subgroup ((ι → OddMarkerGroup) × D)) (χ : SignLabel H) :
    DiagonalIsotypeProjection.CharacterLabel (scalar H) :=
  ⟨fun h => OddMarkerTernaryChart.signScalar (χ.1 h), by
    obtain ⟨i, hi⟩ := χ.2
    exact ⟨i, congrArg (fun s : H →* Multiplicative (ZMod 2) =>
      fun h => OddMarkerTernaryChart.signScalar (s h)) hi⟩⟩

theorem scalarLabel_bijective (H : Subgroup ((ι → OddMarkerGroup) × D)) :
    Function.Bijective (scalarLabel H) := by
  constructor
  · intro χ ψ h
    apply Subtype.ext
    apply (OddMarkerTernaryChart.signScalar_characters_eq_iff χ.1 ψ.1).mp
    exact congrArg Subtype.val h
  · rintro ⟨f, i, rfl⟩
    exact ⟨⟨signCharacter H i, ⟨i, rfl⟩⟩, rfl⟩

def scalarLabelEquiv (H : Subgroup ((ι → OddMarkerGroup) × D)) :
    SignLabel H ≃ DiagonalIsotypeProjection.CharacterLabel (scalar H) :=
  Equiv.ofBijective (scalarLabel H) (scalarLabel_bijective H)

def signProjection (H : Subgroup ((ι → OddMarkerGroup) × D)) (χ : SignLabel H) :
    (ι → ZMod 3) →ₗ[ZMod 3] (ι → ZMod 3) :=
  DiagonalIsotypeProjection.isotypeProjection (scalar H) (scalarLabel H χ)

@[simp] theorem signProjection_apply (H : Subgroup ((ι → OddMarkerGroup) × D))
    (χ : SignLabel H) (v : ι → ZMod 3) (i : ι) :
    signProjection H χ v i = if signCharacter H i = χ.1 then v i else 0 := by
  change (if (fun h => OddMarkerTernaryChart.signScalar (signCharacter H i h)) =
    (fun h => OddMarkerTernaryChart.signScalar (χ.1 h))
    then v i else 0) = _
  rw [OddMarkerTernaryChart.signScalar_characters_eq_iff]

theorem signProjection_mem [Fintype ι] (H : Subgroup ((ι → OddMarkerGroup) × D))
    (χ : SignLabel H) (v : ι → ZMod 3) (hv : v ∈ kernelSubmodule H) :
    signProjection H χ v ∈ kernelSubmodule H :=
  DiagonalIsotypeProjection.isotypeProjection_mem (scalar H) (kernelSubmodule H)
    (diagonal_mem H) (scalarLabel H χ) v hv

theorem signProjection_idempotent (H : Subgroup ((ι → OddMarkerGroup) × D))
    (χ : SignLabel H) (v : ι → ZMod 3) :
    signProjection H χ (signProjection H χ v) = signProjection H χ v :=
  DiagonalIsotypeProjection.isotypeProjection_idempotent (scalar H) (scalarLabel H χ) v

theorem signProjection_of_ne (H : Subgroup ((ι → OddMarkerGroup) × D))
    (χ ψ : SignLabel H) (hχψ : χ ≠ ψ) (v : ι → ZMod 3) :
    signProjection H χ (signProjection H ψ v) = 0 :=
  DiagonalIsotypeProjection.isotypeProjection_of_ne (scalar H) (scalarLabel H χ)
    (scalarLabel H ψ) (fun h => hχψ ((scalarLabel_bijective H).injective h)) v

/-- Exact reconstruction sums once over each original sign character. -/
theorem sum_signProjection [Fintype ι] (H : Subgroup ((ι → OddMarkerGroup) × D))
    (v : ι → ZMod 3) : (∑ χ : SignLabel H, signProjection H χ v) = v := by
  calc
    (∑ χ : SignLabel H, signProjection H χ v) =
        ∑ ψ : DiagonalIsotypeProjection.CharacterLabel (scalar H),
          DiagonalIsotypeProjection.isotypeProjection (scalar H) ψ v :=
      Fintype.sum_equiv (scalarLabelEquiv H) _ _ (fun _ => rfl)
    _ = v := DiagonalIsotypeProjection.sum_isotypeProjection (scalar H) v

theorem mem_iff_signProjection_mem [Fintype ι]
    (H : Subgroup ((ι → OddMarkerGroup) × D)) (v : ι → ZMod 3) :
    v ∈ kernelSubmodule H ↔ ∀ χ : SignLabel H, signProjection H χ v ∈ kernelSubmodule H := by
  constructor
  · exact fun hv χ => signProjection_mem H χ v hv
  · intro hv
    rw [← sum_signProjection H v]
    exact (kernelSubmodule H).sum_mem (fun χ _ => hv χ)

/-- Full projection is onto each actual coordinate. It does not say that
the coordinates can be chosen independently of one another. -/
theorem coordinate_surjective (hD : IsPGroup 2 D)
    (H : Subgroup ((ι → OddMarkerGroup) × D)) (i : ι)
    (hfull : H.map (coordinate i) = ⊤) :
    Function.Surjective (fun v : kernelSubmodule H => v.1 i) := by
  intro z
  have hm : (OddMarkerTernaryChart.chart (Multiplicative.ofAdd z) : OddMarkerGroup) ∈
      (jointKernel H).map (coordinate i) := by
    rw [jointKernel_coordinate_full hD H i hfull]
    exact (OddMarkerTernaryChart.chart (Multiplicative.ofAdd z)).property
  obtain ⟨x, hx, hxi⟩ := Subgroup.mem_map.mp hm
  obtain ⟨v, hv⟩ := (kernelEquiv H).surjective ⟨x, hx⟩
  refine ⟨v.toAdd, ?_⟩
  have hc := congrArg (fun y : jointKernel H => y.1.1 i) hv
  have he : OddMarkerTernaryChart.chart (Multiplicative.ofAdd (v.toAdd.1 i)) =
      OddMarkerTernaryChart.chart (Multiplicative.ofAdd z) :=
    Subtype.ext (hc.trans hxi)
  exact congrArg Multiplicative.toAdd (OddMarkerTernaryChart.chart.injective he)

end SymmetricSubgroupAsymptotics.RepeatedOddMarkerModule

end
