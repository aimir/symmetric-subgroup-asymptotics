import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeThreeSignedQuotientSource
import SymmetricSubgroupAsymptotics.PrimitiveAffineBinaryExceptionalLocal
import SymmetricSubgroupAsymptotics.BinaryPairFrameTransport

/-!
# The literal pair frame of a natural-S3 signed quotient

After quotienting the correlated regular `C3` translations of an actual
local natural-`S3` component, the remaining local complement is the full
two-point permutation group.  This file retains that complement in every
original block and constructs the resulting binary pair frame on the
literal signed quotient action.  No transitive-action representative or
finite catalogue row enters here.
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

omit [Nontrivial block.Fibre] in
/-- Local degree three leaves exactly two nonidentity translation points. -/
theorem degreeThree_localDegree_eq_two
    (hr : Nat.card block.Fibre = 3) :
    localDegree block = 2 := by
  dsimp only [localDegree]
  omega

/-- In the exact natural-S3 case the literal affine complement, hence its
faithful compressed image, has order two. -/
theorem degreeThree_localQuotient_card_eq_two
    (hr : Nat.card block.Fibre = 3)
    (hcomponent : Nat.card block.Component = 6) :
    Nat.card (LocalQuotient block P) = 2 := by
  rw [localQuotient_card_eq_complement block P]
  have hfactor := (P.isComplement'_complement (origin block)).card_mul
  have hV : Nat.card P.V = 3 := (P.card_eq (origin block)).trans hr
  rw [hV, hcomponent] at hfactor
  omega

/-- The literal order-two local quotient is the full permutation group on
its two retained nonidentity points. -/
theorem degreeThree_localQuotient_pretransitive
    (hr : Nat.card block.Fibre = 3)
    (hcomponent : Nat.card block.Component = 6) :
    MulAction.IsPretransitive (LocalQuotient block P)
      (Fin (localDegree block)) := by
  have hdegree := degreeThree_localDegree_eq_two block hr
  have hcard := degreeThree_localQuotient_card_eq_two block P hr hcomponent
  have htop : (complementAction block P).range = ⊤ := by
    apply (complementAction block P).range.eq_top_of_card_eq
    calc
      Nat.card (complementAction block P).range = 2 := hcard
      _ = Nat.card (Equiv.Perm (Fin (localDegree block))) := by
        rw [Nat.card_perm, Nat.card_fin, hdegree]
        norm_num
  change MulAction.IsPretransitive (complementAction block P).range
    (Fin (localDegree block))
  rw [htop]
  constructor
  intro x y
  refine ⟨⟨Equiv.swap x y, by simp⟩, ?_⟩
  change Equiv.swap x y x = y
  exact Equiv.swap_apply_left x y

/-- The point relabelling used by the literal signed quotient action. -/
def degreeThreeSignedQuotientPointEquiv :
    Fin (localDegree block) × block.Points ≃ Fin (quotientDegree block) := by
  change Fin (localDegree block) × block.Points ≃
    Fin (localDegree block * Fintype.card block.Points)
  exact (Equiv.prodCongr (Equiv.refl (Fin (localDegree block)))
    (Fintype.equivFin block.Points)).trans finProdFinEquiv

/-- Conjugating a permutation by a point relabelling and then pulling the
result back recovers the original point action. -/
private theorem Equiv.symm_permCongrHom_apply_self
    {X Y : Type*} (e : X ≃ Y) (g : Equiv.Perm X) (x : X) :
    e.symm (e.permCongrHom g (e x)) = g x := by
  change e.symm (e.permCongr g (e x)) = g x
  rw [Equiv.permCongr_apply, e.symm_apply_apply, e.symm_apply_apply]

/-- The quotient action identifies the source group with its literal range. -/
noncomputable def degreeThreeSignedQuotientRangeEquiv :
    (preE7NonPairAction w U ⧸ E block P) ≃*
      (quotientAction block P).range :=
  MulEquiv.ofBijective (quotientAction block P).rangeRestrict
    ⟨MonoidHom.rangeRestrict_injective_iff.mpr
        (quotientAction_injective block P),
      (quotientAction block P).rangeRestrict_surjective⟩

/-- Exact-component fullness and the transitive literal block top make the
signed quotient transitive on the two retained points in every block. -/
theorem degreeThreeSignedQuotient_product_pretransitive
    (hr : Nat.card block.Fibre = 3)
    (hcomponent : Nat.card block.Component = 6) :
    ∀ x y : Fin (localDegree block) × block.Points,
      ∃ q : preE7NonPairAction w U ⧸ E block P,
        quotientEmbedding block P q • x = y := by
  letI : MulAction.IsPretransitive block.Top block.Points :=
    block.top_pretransitive
  letI : MulAction.IsPretransitive (LocalQuotient block P)
      (Fin (localDegree block)) :=
    degreeThree_localQuotient_pretransitive block P hr hcomponent
  rintro ⟨x, i⟩ ⟨y, j⟩
  obtain ⟨t, ht⟩ := MulAction.exists_smul_eq block.Top i j
  obtain ⟨a, ha⟩ := binaryAffineQuotientTopMap_surjective block P t
  have haj : (quotientEmbedding block P a).right • i = j := by
    change binaryAffineQuotientTopMap block P a • i = j
    rw [ha]
    exact ht
  let x' : Fin (localDegree block) :=
    (quotientEmbedding block P a).left j • x
  obtain ⟨d, hd⟩ := MulAction.exists_smul_eq
    (LocalQuotient block P) x' y
  obtain ⟨k, hkright, hkleft⟩ :=
    quotientEmbedding_fullComponent block P j d
  have ha_pair : quotientEmbedding block P a • (x, i) = (x', j) := by
    rw [PermutationalWreathProduct.smul_def]
    apply Prod.ext
    · change (quotientEmbedding block P a).left
          ((quotientEmbedding block P a).right • i) • x = x'
      rw [haj]
    · exact haj
  refine ⟨k * a, ?_⟩
  rw [map_mul, mul_smul, ha_pair,
    PermutationalWreathProduct.smul_def, hkright, hkleft]
  exact Prod.ext hd rfl

/-- The actual faithful range of the signed quotient is transitive on its
relabeled `2s` points. -/
theorem degreeThreeSignedQuotientRange_pretransitive
    (hr : Nat.card block.Fibre = 3)
    (hcomponent : Nat.card block.Component = 6) :
    MulAction.IsPretransitive (quotientAction block P).range
      (Fin (quotientDegree block)) := by
  constructor
  intro x y
  let e := degreeThreeSignedQuotientPointEquiv block
  obtain ⟨q, hq⟩ := degreeThreeSignedQuotient_product_pretransitive
    block P hr hcomponent (e.symm x) (e.symm y)
  refine ⟨(quotientAction block P).rangeRestrict q, ?_⟩
  change quotientAction block P q x = y
  simpa only [e, degreeThreeSignedQuotientPointEquiv, quotientAction,
    PermutationalWreathProduct.toFintypePerm,
    PermutationalWreathProduct.toPerm, Equiv.permCongr_apply,
    Equiv.apply_symm_apply, Equiv.symm_apply_apply] using congrArg e hq

/-- Canonical two-element coordinate for the local sign point. -/
def degreeThreeBitEquiv
    (hr : Nat.card block.Fibre = 3) :
    ZMod 2 ≃ Fin (localDegree block) :=
  (Finite.equivFin (ZMod 2)).trans (finCongr (by
    rw [Nat.card_zmod, degreeThree_localDegree_eq_two block hr]))

/-- Pair coordinates on the exact point set used by `quotientAction`. -/
def degreeThreeSignedQuotientPairEquiv
    (hr : Nat.card block.Fibre = 3) :
    block.Points × ZMod 2 ≃ Fin (quotientDegree block) where
  toFun p := degreeThreeSignedQuotientPointEquiv block
    (degreeThreeBitEquiv block hr p.2, p.1)
  invFun x :=
    let p := (degreeThreeSignedQuotientPointEquiv block).symm x
    (p.2, (degreeThreeBitEquiv block hr).symm p.1)
  left_inv := by
    rintro ⟨i, b⟩
    simp
  right_inv := by
    intro x
    simp

/-- The literal top map on the original blocks. -/
def degreeThreeSignedQuotientPairTop :
    (preE7NonPairAction w U ⧸ E block P) →*
      Equiv.Perm block.Points :=
  block.Top.subtype.comp (binaryAffineQuotientTopMap block P)

/-- The signed quotient of the exact natural-S3 component carries the
actual pair frame indexed by the original blocks. -/
noncomputable def degreeThreeSignedQuotientPairFrame
    (hr : Nat.card block.Fibre = 3) :
    BinaryPairFrame (quotientAction block P).range block.Points :=
  BinaryPairFrame.ofEquiv (degreeThreeSignedQuotientRangeEquiv block P)
    (degreeThreeSignedQuotientPairTop block P)
    (degreeThreeSignedQuotientPairEquiv block hr) (by
      intro q p
      rcases p with ⟨i, b⟩
      change
        ((degreeThreeSignedQuotientPairEquiv block hr).symm
          (quotientAction block P q
            (degreeThreeSignedQuotientPairEquiv block hr (i, b)))).1 =
          (quotientEmbedding block P q).right • i
      change
        ((degreeThreeSignedQuotientPointEquiv block).symm
          (quotientAction block P q
            (degreeThreeSignedQuotientPointEquiv block
              (degreeThreeBitEquiv block hr b, i)))).2 =
          (quotientEmbedding block P q).right • i
      have htransport :
          (degreeThreeSignedQuotientPointEquiv block).symm
            (quotientAction block P q
              (degreeThreeSignedQuotientPointEquiv block
                (degreeThreeBitEquiv block hr b, i))) =
            quotientEmbedding block P q •
              (degreeThreeBitEquiv block hr b, i) := by
        let e := degreeThreeSignedQuotientPointEquiv block
        let g : Equiv.Perm
            (Fin (localDegree block) × block.Points) :=
          PermutationalWreathProduct.toPerm
            (D := LocalQuotient block P) (Q := block.Top)
            (I := block.Points) (Lambda := Fin (localDegree block))
            (quotientEmbedding block P q)
        let x := (degreeThreeBitEquiv block hr b, i)
        change e.symm (e.permCongrHom g (e x)) = g x
        exact Equiv.symm_permCongrHom_apply_self e g x
      rw [htransport, PermutationalWreathProduct.smul_def])

/-- Relabel the original blocks by their finite cardinality, retaining the
same literal signed quotient action and every correlated pair flip. -/
noncomputable def degreeThreeSignedQuotientFinPairFrame
    (hr : Nat.card block.Fibre = 3) :
    BinaryPairFrame (quotientAction block P).range
      (Fin (Nat.card block.Points)) :=
  (degreeThreeSignedQuotientPairFrame block P hr).reindex
    (Finite.equivFin block.Points)

/-- Fixed-degree chart of the literal signed quotient.  This is the exact
adapter consumed by a degree-two `s`-pair package: the action is transported
only by the canonical point relabelling, and the source equivalence and pair
frame are retained. -/
structure DegreeThreeSignedQuotientPairChart (s : ℕ) : Type 1 where
  action : Subgroup (Equiv.Perm (Fin (2 * s)))
  sourceEquiv : (preE7NonPairAction w U ⧸ E block P) ≃* action
  frame : BinaryPairFrame action (Fin s)
  pretransitive : MulAction.IsPretransitive action (Fin (2 * s))

/-- Construct the fixed-degree chart from the actual block system. -/
noncomputable def degreeThreeSignedQuotientPairChart
    (hr : Nat.card block.Fibre = 3)
    {s : ℕ} (hs : Nat.card block.Points = s)
    (hcomponent : Nat.card block.Component = 6) :
    DegreeThreeSignedQuotientPairChart block P s := by
  have hq : quotientDegree block = 2 * s := by
    rw [quotientDegree_eq block, hr, hs]
  let e : Fin (quotientDegree block) ≃ Fin (2 * s) := finCongr hq
  let F₀ := degreeThreeSignedQuotientPairFrame block P hr
  let F₁ : BinaryPairFrame
      (relabelSubgroup e (quotientAction block P).range) block.Points :=
    F₀.relabelPoints e
  let F : BinaryPairFrame
      (relabelSubgroup e (quotientAction block P).range) (Fin s) :=
    F₁.reindex (Finite.equivFinOfCardEq hs)
  have htrans₀ := degreeThreeSignedQuotientRange_pretransitive
    block P hr hcomponent
  have htrans : MulAction.IsPretransitive
      (relabelSubgroup e (quotientAction block P).range) (Fin (2 * s)) := by
    constructor
    intro x y
    obtain ⟨g, hg⟩ := htrans₀.exists_smul_eq (e.symm x) (e.symm y)
    refine ⟨BinaryPairFrame.sourceRelabelEquiv
      (U := (quotientAction block P).range) e g, ?_⟩
    change e ((g : Equiv.Perm (Fin (quotientDegree block))) (e.symm x)) = y
    exact (congrArg e hg).trans (e.apply_symm_apply y)
  exact
    { action := relabelSubgroup e (quotientAction block P).range
      sourceEquiv := (degreeThreeSignedQuotientRangeEquiv block P).trans
        (BinaryPairFrame.sourceRelabelEquiv
          (U := (quotientAction block P).range) e)
      frame := F
      pretransitive := htrans }

end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
