import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeThreeLocalBitScalar
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeThreeSignedQuotientPairFrame

/-!
# Reflection of a signed pair-frame bit into the local complement

For the literal degree-three signed quotient before any finite relabelling,
the bit retained by the pair frame is exactly the displacement of bit zero
under the corresponding local component of the quotient wreath embedding.
This is a coordinate identity on the actual action, not an abstract
two-group classification.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineImprimitiveBlockTransfer

variable {w : ℕ} {U : PreE7NonPairActionClass w}
  {basePoint : Fin w}
  (block : OriginalMinimalBlock
    (A := preE7NonPairAction w U) basePoint)
  (P : PrimitiveAffineProfile block.Component block.Fibre)
  [Nontrivial block.Fibre]

private theorem symm_permCongrHom_apply_self
    {X Y : Type*} (e : X ≃ Y) (g : Equiv.Perm X) (x : X) :
    e.symm (e.permCongrHom g (e x)) = g x := by
  change e.symm (e.permCongr g (e x)) = g x
  rw [Equiv.permCongr_apply, e.symm_apply_apply, e.symm_apply_apply]

/-- Before physical-point and block-index relabelling, the pair-frame bit is
the literal local-complement bit at the same original block. -/
theorem degreeThreeSignedQuotientPairFrame_bits_eq_localBit
    (hr : Nat.card block.Fibre = 3)
    (k : (degreeThreeSignedQuotientPairFrame block P hr).top.ker)
    (i : block.Points) :
    (degreeThreeSignedQuotientPairFrame block P hr).bits k i =
      degreeThreeLocalBit block P hr
        ((quotientEmbedding block P
          ((degreeThreeSignedQuotientRangeEquiv block P).symm k.1)).left i) := by
  let F := degreeThreeSignedQuotientPairFrame block P hr
  let q := (degreeThreeSignedQuotientRangeEquiv block P).symm k.1
  let pointEquiv := degreeThreeSignedQuotientPointEquiv block
  let bitEquiv := degreeThreeBitEquiv block hr
  have hkq : degreeThreeSignedQuotientRangeEquiv block P q = k.1 :=
    (degreeThreeSignedQuotientRangeEquiv block P).apply_symm_apply k.1
  have htop : (quotientEmbedding block P q).right = 1 := by
    have hk := k.2
    change degreeThreeSignedQuotientPairTop block P q = 1 at hk
    apply Subtype.ext
    exact hk
  have hright : (quotientEmbedding block P q).right • i = i := by
    rw [htop]
    exact one_smul _ _
  have htransport :
      pointEquiv.symm
        (quotientAction block P q (pointEquiv (bitEquiv 0, i))) =
        quotientEmbedding block P q • (bitEquiv 0, i) := by
    let g : Equiv.Perm (Fin (localDegree block) × block.Points) :=
      PermutationalWreathProduct.toPerm
        (D := LocalQuotient block P) (Q := block.Top)
        (I := block.Points) (Lambda := Fin (localDegree block))
        (quotientEmbedding block P q)
    change pointEquiv.symm (pointEquiv.permCongrHom g
      (pointEquiv (bitEquiv 0, i))) = g (bitEquiv 0, i)
    exact symm_permCongrHom_apply_self pointEquiv g (bitEquiv 0, i)
  have hcalc :
      F.frame.symm ((k.1 : Equiv.Perm (Fin (quotientDegree block)))
        (F.frame (i, 0))) =
        (i, degreeThreeLocalBit block P hr
          ((quotientEmbedding block P q).left i)) := by
    rw [← hkq]
    change
      (let p := pointEquiv.symm
          (quotientAction block P q (pointEquiv (bitEquiv 0, i)));
        (p.2, bitEquiv.symm p.1)) = _
    rw [htransport, PermutationalWreathProduct.smul_def, hright]
    rfl
  have hkernel := F.kernel_action k i 0
  have hpairs :
      (i, F.bits k i) =
        (i, degreeThreeLocalBit block P hr
          ((quotientEmbedding block P q).left i)) := by
    simpa only [zero_add] using hkernel.symm.trans hcalc
  simpa only [q] using congrArg Prod.snd hpairs

/-- For an arbitrary signed-quotient element, the affine bit at a target
block is the literal local-complement bit in that target block.  The kernel
formula above is the fixed-top specialization. -/
theorem degreeThreeSignedQuotientPairFrame_affineTranslation_eq_localBit
    (hr : Nat.card block.Fibre = 3)
    (q : preE7NonPairAction w U ⧸ E block P)
    (i : block.Points) :
    let F := degreeThreeSignedQuotientPairFrame block P hr
    F.affineTranslation (degreeThreeSignedQuotientRangeEquiv block P q) i =
      degreeThreeLocalBit block P hr
        ((quotientEmbedding block P q).left i) := by
  let F := degreeThreeSignedQuotientPairFrame block P hr
  let g := degreeThreeSignedQuotientRangeEquiv block P q
  let pointEquiv := degreeThreeSignedQuotientPointEquiv block
  let bitEquiv := degreeThreeBitEquiv block hr
  let j := (quotientEmbedding block P q).right⁻¹ • i
  have htopEq : F.top g = (quotientEmbedding block P q).right :=
    degreeThreeSignedQuotientPairFrame_top_apply block P hr q
  have htop : F.top g j = i := by
    rw [htopEq]
    simp only [j, smul_inv_smul]
  have htransport :
      pointEquiv.symm
        (quotientAction block P q (pointEquiv (bitEquiv 0, j))) =
        quotientEmbedding block P q • (bitEquiv 0, j) := by
    let a : Equiv.Perm (Fin (localDegree block) × block.Points) :=
      PermutationalWreathProduct.toPerm
        (D := LocalQuotient block P) (Q := block.Top)
        (I := block.Points) (Lambda := Fin (localDegree block))
        (quotientEmbedding block P q)
    change pointEquiv.symm (pointEquiv.permCongrHom a
      (pointEquiv (bitEquiv 0, j))) = a (bitEquiv 0, j)
    exact symm_permCongrHom_apply_self pointEquiv a (bitEquiv 0, j)
  have hcalc :
      F.frame.symm ((g.1 : Equiv.Perm (Fin (quotientDegree block)))
        (F.frame (j, 0))) =
        (i, degreeThreeLocalBit block P hr
          ((quotientEmbedding block P q).left i)) := by
    change
      (let p := pointEquiv.symm
          (quotientAction block P q (pointEquiv (bitEquiv 0, j)));
        (p.2, bitEquiv.symm p.1)) = _
    rw [htransport, PermutationalWreathProduct.smul_def]
    rw [show (quotientEmbedding block P q).right • j = i by
      simpa only [j] using smul_inv_smul
        (quotientEmbedding block P q).right i]
    apply Prod.ext rfl
    simpa only [zero_add] using
      degreeThreeLocalBit_action block P hr
        ((quotientEmbedding block P q).left i) 0
  have haffine := F.affine_action_frame g j 0
  have hpairs :
      (i, F.affineTranslation g i) =
        (i, degreeThreeLocalBit block P hr
          ((quotientEmbedding block P q).left i)) := by
    apply F.frame.injective
    rw [← hcalc]
    simpa only [zero_add, htop, F.frame.apply_symm_apply] using haffine.symm
  exact congrArg Prod.snd hpairs

end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
