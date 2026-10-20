import SymmetricSubgroupAsymptotics.CoinducedPairFiltration
import SymmetricSubgroupAsymptotics.RepresentationUniformHeadExact

/-!
The two actual layers of every correlated point-frame subrepresentation.
The first layer is its pullback under the pair-frame inclusion; the second
is the image of its restricted twisted pair sum. Both are subrepresentations
of the same pair frame. No surjectivity onto the full pair frame is assumed.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CoinducedPairFiltration

variable {G V : Type} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  (H L : Subgroup G) (hHL : H ≤ L)
  (sigma : Representation (ZMod 2) L V)
  (D : TwoCosetData H L hHL)

/-- The literal diagonal layer of a correlated subrepresentation. -/
def diagonalLayer (B : Subrepresentation (pointFrame H L hHL sigma)) :
    Subrepresentation (pairFrame L sigma) where
  toSubmodule := B.toSubmodule.comap (inclusion H L hHL sigma).toLinearMap
  apply_mem_toSubmodule g v hv := by
    change inclusion H L hHL sigma (pairFrame L sigma g v) ∈ B
    rw [Representation.IntertwiningMap.isIntertwining]
    exact B.apply_mem_toSubmodule g hv

/-- The diagonal inclusion has the original correlated module as target. -/
def diagonalLayerInclusion (B : Subrepresentation (pointFrame H L hHL sigma)) :
    (diagonalLayer H L hHL sigma B).toRepresentation.IntertwiningMap
      B.toRepresentation where
  toLinearMap := {
    toFun v := ⟨inclusion H L hHL sigma v.1, v.2⟩
    map_add' v w := Subtype.ext (map_add (inclusion H L hHL sigma) v.1 w.1)
    map_smul' c v := Subtype.ext (map_smul (inclusion H L hHL sigma) c v.1) }
  isIntertwining' g := by
    apply LinearMap.ext
    intro v
    apply Subtype.ext
    exact Representation.IntertwiningMap.isIntertwining _ _
      (inclusion H L hHL sigma) g v.1

/-- The image projection with its original submodule carriers explicit. -/
abbrev restrictedImageProjection
    (B : Subrepresentation (pointFrame H L hHL sigma)) :
    B.toRepresentation.IntertwiningMap
      (subrepresentationPairSum H L hHL sigma D B).range.toRepresentation :=
  RepresentationHeadExact.rangeProjection
    (k := ZMod 2) (G := G) (V := B.toSubmodule)
    (W := Representation.coindV L.subtype sigma)
    (ρ := B.toRepresentation) (σ := pairFrame L sigma)
    (subrepresentationPairSum H L hHL sigma D B)

/-- Restriction preserves exactness when the first term is pulled back and
the last term is the actual image of the restricted pair sum. -/
theorem diagonalLayer_range_eq_kernel
    (B : Subrepresentation (pointFrame H L hHL sigma)) :
    (diagonalLayerInclusion H L hHL sigma B).toLinearMap.range =
      (restrictedImageProjection H L hHL sigma D B).toLinearMap.ker := by
  apply le_antisymm
  · rintro _ ⟨v, rfl⟩
    apply Subtype.ext
    exact pairSum_inclusion H L hHL sigma D v.1
  · intro b hb
    have hsum : pairSum H L hHL sigma D b.1 = 0 :=
      congrArg (fun v : (subrepresentationPairSum H L hHL sigma D B).range.toSubmodule =>
        (v : Representation.coindV L.subtype sigma)) hb
    have hrange : b.1 ∈ (inclusion H L hHL sigma).toLinearMap.range := by
      rw [inclusion_range_eq_pairSum_kernel H L hHL sigma D]
      exact hsum
    obtain ⟨v, hv⟩ := hrange
    have hvB : v ∈ diagonalLayer H L hHL sigma B := by
      change (inclusion H L hHL sigma).toLinearMap v ∈ B
      rw [hv]
      exact b.2
    exact ⟨⟨v, hvB⟩, Subtype.ext hv⟩

include D in
set_option maxHeartbeats 800000 in
/-- A uniform head bound on the genuine pair frame bounds every correlated
subrepresentation of the point frame by twice that number. -/
theorem uniform_head_le_twice
    [Finite G] [FiniteDimensional (ZMod 2) V]
    (cap : ℕ)
    (hpair : ∀ A : Subrepresentation (pairFrame L sigma),
      Module.finrank (ZMod 2)
        (A.toRepresentation.IntertwiningMap
          (Representation.trivial (ZMod 2) G (ZMod 2))) ≤ cap)
    (B : Subrepresentation (pointFrame H L hHL sigma)) :
    Module.finrank (ZMod 2)
      (B.toRepresentation.IntertwiningMap
        (Representation.trivial (ZMod 2) G (ZMod 2))) ≤ 2 * cap := by
  classical
  letI : Fintype G := Fintype.ofFinite G
  letI : FiniteDimensional (ZMod 2)
      (Representation.coindV H.subtype (pointFibre H L hHL sigma)) :=
    FiniteDimensional.of_injective
      (Representation.coindV H.subtype (pointFibre H L hHL sigma)).subtype
      (Representation.coindV H.subtype (pointFibre H L hHL sigma)).subtype_injective
  letI : FiniteDimensional (ZMod 2) (Representation.coindV L.subtype sigma) :=
    FiniteDimensional.of_injective
      (Representation.coindV L.subtype sigma).subtype
      (Representation.coindV L.subtype sigma).subtype_injective
  have h := RepresentationUniformHeadExact.uniform_head_le_add
    (pairFrame L sigma) (pointFrame H L hHL sigma) (pairFrame L sigma)
    (inclusion H L hHL sigma) (pairSum H L hHL sigma D)
    (inclusion_range_eq_pairSum_kernel H L hHL sigma D)
    cap cap hpair hpair B
  exact h.trans_eq (two_mul cap).symm

end SymmetricSubgroupAsymptotics.CoinducedPairFiltration

end
