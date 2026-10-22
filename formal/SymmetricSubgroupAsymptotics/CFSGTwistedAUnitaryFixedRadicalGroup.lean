import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryRadicalGroup
import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryFixedMovingSpan
import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryNaturalRadical

/-! The actual defining-fixed radical subgroup and its surjective vector
quotient. This is an intersection with the literal two-step array group,
not a supplied unitary identification. Its map to the ORIGINAL fixed
source is the proved same-lattice natural/source map. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
open CFSGTwistedANaturalMatrices CFSGTwistedAUnitaryUpperArrays
open CFSGTwistedAUpperUnipotent CFSGTwistedAUnitaryNaturalRadical
open CFSGTwistedAIntervalSource

def blockFixedMatrixHom (q : CFSG.PrimePower) (s : ℕ) :
    naturalFixed (s + 2) q →* (Matrix (Index (Fin (s + 1))) (Index (Fin (s + 1))) (q.Extension 2))ˣ :=
  (Units.map (Matrix.reindexAlgEquiv (q.Extension 2) (q.Extension 2)
    (splitEquiv s).symm).toRingHom.toMonoidHom).comp (fixedMatrixHom q (s + 2))

theorem blockFixedMatrixHom_injective (q : CFSG.PrimePower) (s : ℕ) :
    Function.Injective (blockFixedMatrixHom q s) := by
  intro g h he
  apply Subtype.ext
  apply Subtype.ext
  exact (Units.map_injective
    (Matrix.reindexAlgEquiv (q.Extension 2) (q.Extension 2) (splitEquiv s).symm).injective) he

def fixedRadical (q : CFSG.PrimePower) (s : ℕ) : Subgroup (naturalFixed (s + 2) q) :=
  (arrayGroup (K := q.Extension 2) (J := Fin (s + 1))).comap (blockFixedMatrixHom q s)

def radicalBlockHom (q : CFSG.PrimePower) (s : ℕ) :
    fixedRadical q s →* arrayGroup (K := q.Extension 2) (J := Fin (s + 1)) where
  toFun g := ⟨blockFixedMatrixHom q s g.val, g.property⟩
  map_one' := Subtype.ext (map_one (blockFixedMatrixHom q s))
  map_mul' g h := Subtype.ext (map_mul (blockFixedMatrixHom q s) g.val h.val)

def fixedRadicalParameterHom (q : CFSG.PrimePower) (s : ℕ) :
    fixedRadical q s →* Multiplicative (Fin (s + 1) → q.Extension 2) :=
  vectorParameterHom.comp (radicalBlockHom q s)

theorem blockFixedMatrixHom_radicalElement (q : CFSG.PrimePower) (s : ℕ)
    (v : Fin (s + 1) → q.Extension 2) (b : q.Extension 2) (hb : Condition q s v b) :
    blockFixedMatrixHom q s
      ⟨(radicalElement q s v b hb).val, (radicalElement q s v b hb).property.2⟩ =
        upperUnit (firstRow q s v) v b := by
  apply Units.ext
  change Matrix.reindex (splitEquiv s).symm (splitEquiv s).symm
    (Matrix.reindex (splitEquiv s) (splitEquiv s) (upperArray (firstRow q s v) v b)) = _
  ext i j
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_symm,
    Equiv.symm_apply_apply]
  all_goals rfl

def fixedRadicalElement (q : CFSG.PrimePower) (s : ℕ)
    (v : Fin (s + 1) → q.Extension 2) (b : q.Extension 2) (hb : Condition q s v b) : fixedRadical q s :=
  ⟨⟨(radicalElement q s v b hb).val, (radicalElement q s v b hb).property.2⟩, by
    change blockFixedMatrixHom q s _ ∈ arrayGroup
    rw [blockFixedMatrixHom_radicalElement]
    exact ⟨firstRow q s v, v, b, rfl⟩⟩

theorem fixedRadicalParameterHom_element (q : CFSG.PrimePower) (s : ℕ)
    (v : Fin (s + 1) → q.Extension 2) (b : q.Extension 2) (hb : Condition q s v b) :
    fixedRadicalParameterHom q s (fixedRadicalElement q s v b hb) = Multiplicative.ofAdd v := by
  change Multiplicative.ofAdd (fun i =>
    (blockFixedMatrixHom q s
      ⟨(radicalElement q s v b hb).val, (radicalElement q s v b hb).property.2⟩ :
        Matrix (Index (Fin (s + 1))) (Index (Fin (s + 1))) (q.Extension 2))
          (.inr (.inl i)) (.inr (.inr ()))) = _
  rw [blockFixedMatrixHom_radicalElement]
  rfl

theorem fixedRadicalParameterHom_surjective (q : CFSG.PrimePower) (s : ℕ) :
    Function.Surjective (fixedRadicalParameterHom q s) := by
  intro v
  obtain ⟨b, hb⟩ := condition_exists q s v.toAdd
  exact ⟨fixedRadicalElement q s v.toAdd b hb,
    (fixedRadicalParameterHom_element q s v.toAdd b hb).trans (ofAdd_toAdd v)⟩

def naturalFixedToOriginal (q : CFSG.PrimePower) (r : ℕ) : naturalFixed r q →* Fixed r q where
  toFun g := fixedElementOfNaturalUnit r q g.val g.property
  map_one' := by
    apply Subtype.ext
    exact congrArg (fun g : CFSG.Models.Chevalley.Model (CartanMatrix.A r) (q.Extension 2) => g.val)
      (map_one (elementaryToModel (q.Extension 2) r))
  map_mul' g h := by
    apply Subtype.ext
    exact congrArg (fun u : CFSG.Models.Chevalley.Model (CartanMatrix.A r) (q.Extension 2) => u.val)
      (map_mul (elementaryToModel (q.Extension 2) r) g.val h.val)

def radicalToOriginal (q : CFSG.PrimePower) (s : ℕ) : fixedRadical q s →* Fixed (s + 2) q :=
  (naturalFixedToOriginal q (s + 2)).comp (fixedRadical q s).subtype

end SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
