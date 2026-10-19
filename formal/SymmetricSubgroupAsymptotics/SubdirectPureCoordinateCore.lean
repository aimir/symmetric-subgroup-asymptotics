import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Algebra.Group.Prod

/-! Pure-coordinate kernels in an actual subdirect product. A nontrivial
pure word is an essential input: surjectivity of the projections alone
also permits diagonal subgroups. No normal-generator bound is assumed. -/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics
namespace SubdirectPureCoordinateCore

/-- The actual opposite-coordinate kernel. -/
def rightPure {L R : Type*} [Group L] [Group R]
    (K : Subgroup (L × R)) : Subgroup R :=
  K.comap (MonoidHom.inr L R)

/-- Surjectivity onto the opposite component makes its pure kernel normal. -/
theorem rightPure_normal {L R : Type*} [Group L] [Group R]
    (K : Subgroup (L × R))
    (hright : ∀ r : R, ∃ l : L, (l,r) ∈ K) :
    (rightPure K).Normal where
  conj_mem n hn r := by
    obtain ⟨l,hl⟩ := hright r
    change ((1 : L), r * n * r⁻¹) ∈ K
    have h := K.mul_mem (K.mul_mem hl hn) (K.inv_mem hl)
    simpa [mul_assoc] using h

/-- The nontrivial pure element can be an evaluated original generator
word. Its membership and nonidentity are separate finite obligations. -/
theorem rightPure_ne_bot {L R : Type*} [Group L] [Group R]
    (K : Subgroup (L × R)) (r : R)
    (hpure : ((1 : L),r) ∈ K) (hne : r ≠ 1) : rightPure K ≠ ⊥ := by
  intro hbot
  apply hne
  have hr : r ∈ rightPure K := hpure
  rw [hbot] at hr
  exact Subgroup.mem_bot.mp hr

/-- Apply an existing component's actual unique-minimal-normal theorem to
the proved pure kernel. This is a structural socle inclusion, not a final
quotient-capacity hypothesis. -/
theorem right_core_le {L R : Type*} [Group L] [Group R]
    (K : Subgroup (L × R))
    (hright : ∀ r : R, ∃ l : L, (l,r) ∈ K)
    (T : Subgroup R)
    (hcore : ∀ N : Subgroup R, N.Normal → N ≠ ⊥ → T ≤ N)
    (r : R) (hpure : ((1 : L),r) ∈ K) (hne : r ≠ 1) :
    ∀ t : R, t ∈ T → ((1 : L),t) ∈ K := by
  exact hcore (rightPure K) (rightPure_normal K hright)
    (rightPure_ne_bot K r hpure hne)

end SubdirectPureCoordinateCore
end SymmetricSubgroupAsymptotics
