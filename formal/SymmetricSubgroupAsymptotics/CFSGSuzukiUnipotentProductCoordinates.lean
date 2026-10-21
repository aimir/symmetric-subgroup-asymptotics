import SymmetricSubgroupAsymptotics.CFSGSuzukiUnipotentProduct

/-! Exact coordinates of the same actual Borel envelope, read directly
from its first column. No order of the whole Suzuki group is asserted. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGSuzukiUnipotent
open CFSGSuzukiFieldParameters CFSGSuzukiTorus CFSG.Models.SuzukiConstruction

theorem product_firstColumn (m : ℕ) (a b : CFSGSuzukiFieldParameters.Field m)
    (c : (CFSGSuzukiFieldParameters.Field m)ˣ) :
    ((unipotentElement m a b * normalizedTorusElement m c : Ambient m) : Mat m) 0 0 = (c : CFSGSuzukiFieldParameters.Field m) ∧
    ((unipotentElement m a b * normalizedTorusElement m c : Ambient m) : Mat m) 1 0 = a * c ∧
    ((unipotentElement m a b * normalizedTorusElement m c : Ambient m) : Mat m) 2 0 = b * c := by
  simp [Matrix.GeneralLinearGroup.coe_mul, unipotentElement_coe, normalizedTorusElement_coe,
    diagonalTorus, Matrix.mul_diagonal, unipotent]

def borelParameterMap (m : ℕ)
    (x : (CFSGSuzukiFieldParameters.Field m × CFSGSuzukiFieldParameters.Field m) ×
      (CFSGSuzukiFieldParameters.Field m)ˣ) : borelEnvelope m :=
  ⟨unipotentElement m x.1.1 x.1.2 * normalizedTorusElement m x.2,
    (borelEnvelope m).mul_mem
      (unipotentSubgroup_le_borelEnvelope m ⟨_, _, rfl⟩)
      (normalizedTorus_mem_borelEnvelope m x.2)⟩

theorem borelParameterMap_injective (m : ℕ) : Function.Injective (borelParameterMap m) := by
  rintro ⟨⟨a, b⟩, c⟩ ⟨⟨d, e⟩, f⟩ h
  have h0 := congrArg (fun g : borelEnvelope m => (g.val : Mat m) 0 0) h
  have h1 := congrArg (fun g : borelEnvelope m => (g.val : Mat m) 1 0) h
  have h2 := congrArg (fun g : borelEnvelope m => (g.val : Mat m) 2 0) h
  change ((unipotentElement m a b * normalizedTorusElement m c : Ambient m) : Mat m) 0 0 =
    ((unipotentElement m d e * normalizedTorusElement m f : Ambient m) : Mat m) 0 0 at h0
  rw [(product_firstColumn m a b c).1, (product_firstColumn m d e f).1] at h0
  have hcf : c = f := Units.ext h0
  subst f
  change ((unipotentElement m a b * normalizedTorusElement m c : Ambient m) : Mat m) 1 0 =
    ((unipotentElement m d e * normalizedTorusElement m c : Ambient m) : Mat m) 1 0 at h1
  rw [(product_firstColumn m a b c).2.1, (product_firstColumn m d e c).2.1] at h1
  change ((unipotentElement m a b * normalizedTorusElement m c : Ambient m) : Mat m) 2 0 =
    ((unipotentElement m d e * normalizedTorusElement m c : Ambient m) : Mat m) 2 0 at h2
  rw [(product_firstColumn m a b c).2.2, (product_firstColumn m d e c).2.2] at h2
  have had : a = d := mul_right_cancel₀ (Units.ne_zero c) h1
  have hbe : b = e := mul_right_cancel₀ (Units.ne_zero c) h2
  subst d
  subst e
  rfl

def borelParameterEquiv (m : ℕ) :
    ((CFSGSuzukiFieldParameters.Field m × CFSGSuzukiFieldParameters.Field m) ×
      (CFSGSuzukiFieldParameters.Field m)ˣ) ≃ borelEnvelope m :=
  Equiv.ofBijective (borelParameterMap m) ⟨borelParameterMap_injective m, by
    intro g
    obtain ⟨a, b, c, hg⟩ := borelEnvelope_factor m g.val g.property
    exact ⟨((a, b), c), Subtype.ext hg.symm⟩⟩

theorem borelEnvelope_card (m : ℕ) :
    Nat.card (borelEnvelope m) = Nat.card (CFSGSuzukiFieldParameters.Field m) ^ 2 *
      Nat.card ((CFSGSuzukiFieldParameters.Field m)ˣ) := by
  rw [Nat.card_congr (borelParameterEquiv m).symm, Nat.card_prod, Nat.card_prod, pow_two]

end SymmetricSubgroupAsymptotics.CFSGSuzukiUnipotent
