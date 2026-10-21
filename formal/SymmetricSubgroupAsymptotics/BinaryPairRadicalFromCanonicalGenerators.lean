import SymmetricSubgroupAsymptotics.BinaryPairCanonicalAffinePermutation
import SymmetricSubgroupAsymptotics.RepresentationRadicalFromActualGeneratorBasis
import SymmetricSubgroupAsymptotics.ActualGeneratorTupleFromFaithfulImage
import SymmetricSubgroupAsymptotics.RepresentationCoordinateChangeRadical

/-! Sparse canonical affine generators identify the whole intrinsic
radical on the original source, using only generator/basis columns.
Canonical labels retain every original point and actual group element. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryPairFrame
local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
variable {X : Type} [Finite X] {U : Subgroup (Equiv.Perm X)}
    (E : BinaryPairFrame U (Fin 8))

/-- The generator completeness premise is the literal same-source image
identity proved separately by sparse kernel and top generator words. -/
theorem original_radical_eq_of_canonical_affine_generators_basis {r d q c : ℕ}
    (hzero : U = E.splitAffineAction)
    (t : Fin r → Equiv.Perm (Fin 8)) (a : Fin r → Fin 8 → ZMod 2)
    (ht : ∀ i, t i ∈ E.top.range) (ha : ∀ i, a i ∈ E.kernelSpace)
    (hgen : U.map E.canonicalPointLabels.permCongrHom = Subgroup.closure
      (Set.range fun i => binaryEightCanonicalPairFrame.affinePermutation (t i) (a i)))
    (W : Subrepresentation (permutationFunctionRepresentation (ZMod 2) U X))
    (S : BinaryCoordinateSpace 16 d) (R : BinaryCoordinateSpace 16 q)
    (hW : (E.originalCoordinateSubrepresentation W).toSubmodule = S.space)
    (hbasis : ∀ i j,
      ((pairLayerFlatten (w := 8)).toLinearMap.comp
        ((affinePairLayerMap (t i) (a i)).comp
          (pairLayerFlatten (w := 8)).symm.toLinearMap)) (S.inclusion (Pi.single j 1)) -
        S.inclusion (Pi.single j 1) ∈ R.space)
    (hcap : Module.finrank (ZMod 2) W.toRepresentation.Coinvariants ≤ c)
    (hdim : d = q+c) :
    ((Representation.Coinvariants.ker W.toRepresentation).map W.toSubmodule.subtype).map
      E.originalCoordinateEquiv.toLinearMap = R.space := by
  let u : Fin r → U := fun i => E.originalZeroRow hzero ⟨t i,ht i⟩ (a i) (ha i)
  let e := E.canonicalPointLabels.permCongrHom
  let j : U →* Equiv.Perm (Fin 16) := e.toMonoidHom.comp U.subtype
  let g : Fin r → Equiv.Perm (Fin 16) := fun i =>
    binaryEightCanonicalPairFrame.affinePermutation (t i) (a i)
  have hj : Function.Injective j := e.injective.comp Subtype.val_injective
  have hju (i : Fin r) : j (u i) = g i := E.canonical_affinePermutation _ _
  have hrange : j.range = U.map e.toMonoidHom := by
    ext p
    constructor
    · rintro ⟨b,rfl⟩;exact ⟨b.val,b.property,rfl⟩
    · rintro ⟨b,hb,rfl⟩;exact ⟨⟨b,hb⟩,rfl⟩
  obtain ⟨v,hv,hfull⟩ := exists_actual_generating_tuple_of_injective_image j hj g
    (hrange.trans hgen)
  have he : v = u := funext fun i => hj ((hv i).trans (hju i).symm)
  rw [he] at hfull
  have hact (i : Fin r) : E.originalCoordinateRepresentation (u i) =
      (pairLayerFlatten (w := 8)).toLinearMap.comp
        ((affinePairLayerMap (t i) (a i)).comp (pairLayerFlatten (w := 8)).symm.toLinearMap) :=
    E.originalCoordinateRepresentation_zeroRow hzero ⟨t i,ht i⟩ _ (ha i)
  have hc : Module.finrank (ZMod 2)
      (E.originalCoordinateSubrepresentation W).toRepresentation.Coinvariants ≤ c := by
    rw [← E.originalCoordinateSubrepresentation_head W];exact hcap
  have hr := representation_radical_eq_of_actual_generators_basis E.originalCoordinateRepresentation
    (E.originalCoordinateSubrepresentation W) S R u hfull hW
    (fun i l => by rw [hact];exact hbasis i l) hc hdim
  exact (RepresentationCoordinateChange.subrepresentation_radical
    (permutationFunctionRepresentation (ZMod 2) U X) E.originalCoordinateEquiv W).trans hr

end SymmetricSubgroupAsymptotics.BinaryPairFrame
