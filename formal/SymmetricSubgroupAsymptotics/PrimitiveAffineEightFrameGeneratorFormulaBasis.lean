import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameInducedCoordinates

/-!
# Check an eight-frame generator formula on a basis

Both sides of the generated Schreier formula are linear in the sixteen
binary coordinates.  It is therefore enough for generated certificates to
check the sixteen coordinate vectors, instead of enumerating all `2^16`
vectors separately for every generator, block and local coordinate.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics

theorem binaryFrameGeneratorFormula_of_basis
    {G L J : Type} [Group G] [Group L]
    (modelRepresentation :
      Representation (ZMod 2) G (Fin 16 → ZMod 2))
    (localRepresentation :
      Representation (ZMod 2) L (Fin 2 → ZMod 2))
    (ambient : J → G)
    (localValue : J → Fin 8 → L)
    (next : J → Fin 8 → Fin 8)
    (h_basis : ∀ (j : J) (a : Fin 8) (i : Fin 2) (k : Fin 16),
      modelRepresentation (ambient j)
          (Pi.single k (1 : ZMod 2) : Fin 16 → ZMod 2)
          (CoinducedLeadingCoordinates.label a i) =
        localRepresentation (localValue j a)
          (fun q ↦ (Pi.single k (1 : ZMod 2) : Fin 16 → ZMod 2)
            (CoinducedLeadingCoordinates.label (next j a) q)) i) :
    ∀ (j : J) (v : Fin 16 → ZMod 2) (a : Fin 8) (i : Fin 2),
      modelRepresentation (ambient j) v
          (CoinducedLeadingCoordinates.label a i) =
        localRepresentation (localValue j a)
          (fun q ↦ v
            (CoinducedLeadingCoordinates.label (next j a) q)) i := by
  intro j v a i
  let restriction :
      (Fin 16 → ZMod 2) →ₗ[ZMod 2] (Fin 2 → ZMod 2) :=
    LinearMap.pi (fun q ↦ LinearMap.proj
      (CoinducedLeadingCoordinates.label (next j a) q))
  let lhs : (Fin 16 → ZMod 2) →ₗ[ZMod 2] ZMod 2 :=
    (LinearMap.proj (CoinducedLeadingCoordinates.label a i)).comp
      (modelRepresentation (ambient j))
  let rhs : (Fin 16 → ZMod 2) →ₗ[ZMod 2] ZMod 2 :=
    (LinearMap.proj i).comp
      ((localRepresentation (localValue j a)).comp restriction)
  have hmaps : lhs = rhs := by
    apply (Pi.basisFun (ZMod 2) (Fin 16)).ext
    intro k
    rw [Pi.basisFun_apply]
    exact h_basis j a i k
  exact LinearMap.congr_fun hmaps v

end SymmetricSubgroupAsymptotics

end
