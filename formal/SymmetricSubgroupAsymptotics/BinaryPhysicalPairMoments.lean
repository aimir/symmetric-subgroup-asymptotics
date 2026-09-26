import SymmetricSubgroupAsymptotics.BinaryPhysicalPairCertificate
import SymmetricSubgroupAsymptotics.JointSourceGraphs

/-! The exact quotient cover in a physical pair certificate supplies the
common-source moment for its central-marker weight. Every power retains one
complete original source subgroup. This proves the moment and nonnegativity
inputs for that weight; the corresponding local counting envelope remains a
separate obligation. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics
namespace BinaryPhysicalPairCertificate

variable {w : ℕ} {U : Subgroup (Equiv.Perm (Fin w))} {N : Subgroup U} [N.Normal]
    (C : BinaryPhysicalPairCertificate U N)

/-- The actual quotient by the original pair kernel and original normal. -/
abbrev momentQuotient : Type := U ⧸ (C.frame.top.ker ⊔ N)

/-- Descend the recorded physical cover through its exact kernel. -/
def momentCover : C.momentQuotient →* Equiv.Perm (Fin C.localCertificate.coverDegree) :=
  QuotientGroup.lift (C.frame.top.ker ⊔ N) C.localCertificate.cover
    C.localCertificate.cover_kernel.symm.le

@[simp] theorem momentCover_original (u : U) :
    C.momentCover (QuotientGroup.mk' (C.frame.top.ker ⊔ N) u)=
      C.localCertificate.cover u := rfl

/-- Faithfulness follows from the recorded kernel equality; it is not an
additional hypothesis about the quotient or a replacement representation. -/
theorem momentCover_injective : Function.Injective C.momentCover := by
  rw [← MonoidHom.ker_eq_bot_iff, momentCover, QuotientGroup.ker_lift,
    C.localCertificate.cover_kernel, QuotientGroup.map_mk'_self]

/-- The quotient epimorphisms and all binary marker characters are on the
same complete source J. The central marker is retained inside the weight. -/
def momentWeight (J : Type*) [Group J] : ℝ :=
  (Nat.card (GroupEpimorphism J C.momentQuotient) : ℝ)*
    (2 : ℝ)^(C.localCertificate.cutDimension*binaryCharacterRank J)

theorem momentWeight_nonneg (J : Type*) [Group J] : 0≤C.momentWeight J := by
  unfold momentWeight
  positivity

/-- Encode all q quotient/marker columns jointly over one literal J≤S_b.
Repeated maps and dependent characters are allowed. The original exterior
has degree b, and every column uses exactly s+2c new physical points, where
s and c are the cover degree and cut dimension of this certificate. This
requires neither a supplied moment bound nor bounded total subgroup counts. -/
theorem momentWeight_moment_le (b q : ℕ) :
    (∑ J : Subgroup (Equiv.Perm (Fin b)), C.momentWeight J^q) ≤
      (subgroupCount (b+q*(C.localCertificate.coverDegree+
        2*C.localCertificate.cutDimension)) : ℝ) := by
  have hm := jointSourceEpimorphism_binaryRank_moment_le
    C.momentCover C.momentCover_injective
    (MonoidHom.id C.momentQuotient) Function.surjective_id
    b C.localCertificate.cutDimension q
  unfold momentWeight
  exact_mod_cast hm

end BinaryPhysicalPairCertificate
end SymmetricSubgroupAsymptotics
