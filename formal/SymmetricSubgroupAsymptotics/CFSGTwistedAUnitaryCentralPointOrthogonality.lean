import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCentralPointAction
import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryRootLineCommutation

/-! Original projective automorphisms preserve actual signed-Hermitian
orthogonality of their central-point labels, because it is exactly the
intrinsic commutation relation of the corresponding Sylow centres. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
open CFSGTwistedAUpperUnipotent CFSGTwistedAUnitaryParameters CFSGSubgroupPairCommutation
open CFSGSerreOrdinaryTwists

def unitaryCentralPointOrthogonal (q : CFSG.PrimePower) (s : ℕ)
    (P Q : unitaryCentralPoints q s) : Prop :=
  ∀ v ∈ P.val, ∀ w ∈ Q.val, unitaryNaturalPair q (s + 3) v w = 0

theorem unitaryCentralPointOrthogonal_iff_pair (q : CFSG.PrimePower) (s : ℕ)
    (P Q : unitaryCentralPoints q s) (g h : naturalFixed (s + 3) q)
    (hg : conjugateCentralPoint q (s + 1) g = P.val)
    (hh : conjugateCentralPoint q (s + 1) h = Q.val) :
    unitaryCentralPointOrthogonal q s P Q ↔
      unitaryNaturalPair q (s + 3) (unitaryCentralVector q s g) (unitaryCentralVector q s h) = 0 := by
  have hp : P.val = (q.Extension 2) ∙ unitaryCentralVector q s g :=
    hg.symm.trans (conjugateCentralPoint_eq_span q (s + 1) g)
  have hq : Q.val = (q.Extension 2) ∙ unitaryCentralVector q s h :=
    hh.symm.trans (conjugateCentralPoint_eq_span q (s + 1) h)
  constructor
  · intro ho
    apply ho
    · rw [hp]
      exact Submodule.mem_span_singleton_self _
    · rw [hq]
      exact Submodule.mem_span_singleton_self _
  · intro hz v hv w hw
    rw [hp] at hv
    rw [hq] at hw
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hv
    obtain ⟨b, hb⟩ := Submodule.mem_span_singleton.mp hw
    rw [← ha, ← hb]
    change hermitianPair (definingFieldAutomorphism q 2) _ (a • _) (b • _) = 0
    rw [hermitianPair_smul]
    change definingFieldAutomorphism q 2 a * b *
      unitaryNaturalPair q (s + 3) (unitaryCentralVector q s g) (unitaryCentralVector q s h) = 0
    rw [hz, mul_zero]

theorem allCommute_labels_iff_orthogonal (q : CFSG.PrimePower) (s : ℕ)
    (P Q : unitaryCentralPoints q s) :
    AllCommute (unitaryCentralPointLabel q s P) (unitaryCentralPointLabel q s Q) ↔
      unitaryCentralPointOrthogonal q s P Q := by
  let g : naturalFixed (s + 3) q := Classical.choose P.property
  let h : naturalFixed (s + 3) q := Classical.choose Q.property
  rw [unitaryCentralPointLabel_representative q s P g (Classical.choose_spec P.property),
    unitaryCentralPointLabel_representative q s Q h (Classical.choose_spec Q.property)]
  exact (conjugate_projective_rootLines_allCommute_iff q s g h).trans
    (unitaryCentralPointOrthogonal_iff_pair q s P Q g h
      (Classical.choose_spec P.property) (Classical.choose_spec Q.property)).symm

theorem unitaryCentralPointAction_preserves_orthogonality (q : CFSG.PrimePower) (s : ℕ)
    (f : MulAut (CFSG.Models.TwistedA (s + 3) q)) (P Q : unitaryCentralPoints q s) :
    unitaryCentralPointOrthogonal q s (unitaryCentralPointActionHom q s f P)
        (unitaryCentralPointActionHom q s f Q) ↔ unitaryCentralPointOrthogonal q s P Q := by
  calc
    _ ↔ AllCommute
        (unitaryCentralPointLabel q s (unitaryCentralPointActionHom q s f P))
        (unitaryCentralPointLabel q s (unitaryCentralPointActionHom q s f Q)) :=
      (allCommute_labels_iff_orthogonal q s _ _).symm
    _ ↔ AllCommute ((unitaryCentralPointLabel q s P).map f.toMonoidHom)
        ((unitaryCentralPointLabel q s Q).map f.toMonoidHom) := by
      rw [unitaryCentralPointAction_label, unitaryCentralPointAction_label]
    _ ↔ AllCommute (unitaryCentralPointLabel q s P) (unitaryCentralPointLabel q s Q) :=
      allCommute_map_iff f.toMonoidHom f.injective _ _
    _ ↔ _ := allCommute_labels_iff_orthogonal q s P Q

end SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
