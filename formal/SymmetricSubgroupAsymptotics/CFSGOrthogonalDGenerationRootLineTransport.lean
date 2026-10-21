import SymmetricSubgroupAsymptotics.CFSGOrthogonalDGenerationMonomialAction

/-! Full-parameter sparse root-line transport inside the SAME subgroup
of actual matrix units. In the cleaned-word variant W itself need not
belong to the subgroup: the retained generator A*W suffices when A
commutes with the output line. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDGenerationRootLineTransport
variable {K I : Type*} [Field K] [Fintype I] [DecidableEq I]

def HasRootLine (H : Subgroup (Matrix I I K)ˣ) (A : K → Matrix I I K) : Prop :=
  ∀ a, ∃ g : (Matrix I I K)ˣ, g ∈ H ∧ (g : Matrix I I K) = A a

theorem conjugate_transfer (H : Subgroup (Matrix I I K)ˣ)
    (Y : (Matrix I I K)ˣ) (hY : Y ∈ H) (A B : K → Matrix I I K)
    (c : K) (hc : c ≠ 0)
    (hconj : ∀ a, (Y : Matrix I I K) * A a * (↑Y⁻¹ : Matrix I I K) = B (c * a))
    (hA : HasRootLine H A) : HasRootLine H B := by
  intro b
  obtain ⟨g, hg, he⟩ := hA (b / c)
  refine ⟨Y * g * Y⁻¹, H.mul_mem (H.mul_mem hY hg) (H.inv_mem hY), ?_⟩
  change (Y : Matrix I I K) * (g : Matrix I I K) * (↑Y⁻¹ : Matrix I I K) = B b
  rw [he, hconj, mul_div_cancel₀ _ hc]

theorem inverse_conjugate_transfer (H : Subgroup (Matrix I I K)ˣ)
    (Y : (Matrix I I K)ˣ) (hY : Y ∈ H) (A B : K → Matrix I I K)
    (c : K)
    (hconj : ∀ a, (Y : Matrix I I K) * A a * (↑Y⁻¹ : Matrix I I K) = B (c * a))
    (hB : HasRootLine H B) : HasRootLine H A := by
  intro a
  obtain ⟨g, hg, he⟩ := hB (c * a)
  refine ⟨Y⁻¹ * g * Y, H.mul_mem (H.mul_mem (H.inv_mem hY) hg) hY, ?_⟩
  change (↑Y⁻¹ : Matrix I I K) * (g : Matrix I I K) * (Y : Matrix I I K) = A a
  rw [he, ← hconj]
  simp only [mul_assoc, Units.inv_mul, mul_one]
  rw [← mul_assoc, Units.inv_mul, one_mul]

theorem cleaned_word_conjugation (A W : (Matrix I I K)ˣ)
    (X Z : K → Matrix I I K) (c : K)
    (hW : ∀ a, (W : Matrix I I K) * X a * (↑W⁻¹ : Matrix I I K) = Z (c * a))
    (hcomm : ∀ b, Commute (A : Matrix I I K) (Z b)) (a : K) :
    ((A * W : (Matrix I I K)ˣ) : Matrix I I K) * X a *
      (↑((A * W)⁻¹) : Matrix I I K) = Z (c * a) := by
  calc
    ((A * W : (Matrix I I K)ˣ) : Matrix I I K) * X a *
        (↑((A * W)⁻¹) : Matrix I I K) =
        (A : Matrix I I K) * ((W : Matrix I I K) * X a * (↑W⁻¹ : Matrix I I K)) *
          (↑A⁻¹ : Matrix I I K) := by
            simp only [_root_.mul_inv_rev, Units.val_mul, mul_assoc]
    _ = (A : Matrix I I K) * Z (c * a) * (↑A⁻¹ : Matrix I I K) := by rw [hW]
    _ = Z (c * a) := by
      rw [(hcomm (c * a)).eq, mul_assoc, Units.mul_inv, mul_one]

theorem cleaned_word_transfer (H : Subgroup (Matrix I I K)ˣ)
    (A W : (Matrix I I K)ˣ) (hY : A * W ∈ H)
    (X Z : K → Matrix I I K) (c : K) (hc : c ≠ 0)
    (hW : ∀ a, (W : Matrix I I K) * X a * (↑W⁻¹ : Matrix I I K) = Z (c * a))
    (hcomm : ∀ b, Commute (A : Matrix I I K) (Z b))
    (hX : HasRootLine H X) : HasRootLine H Z :=
  conjugate_transfer H (A * W) hY X Z c hc
    (cleaned_word_conjugation A W X Z c hW hcomm) hX

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDGenerationRootLineTransport
