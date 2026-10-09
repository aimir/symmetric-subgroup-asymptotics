import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameInducedCoordinates

/-!
# Check a binary induced-frame generator formula on a basis

Both sides of the Schreier formula are linear in the frame coordinates.
This reusable theorem reduces a generated identity to the coordinate basis,
avoiding enumeration of the full binary module.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics

theorem binaryInducedFrameGeneratorFormula_of_basis
    {G L J : Type} [Group G] [Group L]
    (m : ℕ)
    (modelRepresentation :
      Representation (ZMod 2) G (Fin (m * 2) → ZMod 2))
    (localRepresentation :
      Representation (ZMod 2) L (Fin 2 → ZMod 2))
    (ambient : J → G)
    (localValue : J → Fin m → L)
    (next : J → Fin m → Fin m)
    (h_basis : ∀ (j : J) (a : Fin m) (i : Fin 2) (k : Fin (m * 2)),
      modelRepresentation (ambient j)
          (Pi.single k (1 : ZMod 2) : Fin (m * 2) → ZMod 2)
          (CoinducedLeadingCoordinates.label a i) =
        localRepresentation (localValue j a)
          (fun q ↦ (Pi.single k (1 : ZMod 2) : Fin (m * 2) → ZMod 2)
            (CoinducedLeadingCoordinates.label (next j a) q)) i) :
    ∀ (j : J) (v : Fin (m * 2) → ZMod 2) (a : Fin m) (i : Fin 2),
      modelRepresentation (ambient j) v
          (CoinducedLeadingCoordinates.label a i) =
        localRepresentation (localValue j a)
          (fun q ↦ v
            (CoinducedLeadingCoordinates.label (next j a) q)) i := by
  intro j v a i
  let restriction :
      (Fin (m * 2) → ZMod 2) →ₗ[ZMod 2] (Fin 2 → ZMod 2) :=
    LinearMap.pi (fun q ↦ LinearMap.proj
      (CoinducedLeadingCoordinates.label (next j a) q))
  let lhs : (Fin (m * 2) → ZMod 2) →ₗ[ZMod 2] ZMod 2 :=
    (LinearMap.proj (CoinducedLeadingCoordinates.label a i)).comp
      (modelRepresentation (ambient j))
  let rhs : (Fin (m * 2) → ZMod 2) →ₗ[ZMod 2] ZMod 2 :=
    (LinearMap.proj i).comp
      ((localRepresentation (localValue j a)).comp restriction)
  have hmaps : lhs = rhs := by
    apply (Pi.basisFun (ZMod 2) (Fin (m * 2))).ext
    intro k
    rw [Pi.basisFun_apply]
    exact h_basis j a i k
  exact LinearMap.congr_fun hmaps v

end SymmetricSubgroupAsymptotics

end
