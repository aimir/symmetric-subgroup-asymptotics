import SymmetricSubgroupAsymptotics.InducedMackeyDecomposition
import SymmetricSubgroupAsymptotics.InducedDoubleCosetIndices
import SymmetricSubgroupAsymptotics.RepresentationCoordinateHeads
import SymmetricSubgroupAsymptotics.TraceyTernaryPrimePower

/-! The actual Sylow/Mackey filtration gives the general ternary Gaussian
bound from the explicit published prime-power input. All coordinate
pieces use the original twisted fibre; the actual source is an arbitrary
subrepresentation of the original induced module. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical BigOperators
namespace SymmetricSubgroupAsymptotics

def representationRestrictionHom {k G P V A : Type} [Field k]
    [Group G] [Group P] [AddCommGroup V] [Module k V]
    [AddCommGroup A] [Module k A]
    (ρ : Representation k G V) (σ : Representation k G A) (φ : P→*G) :
    (ρ.IntertwiningMap σ)→ₗ[k] (Representation.IntertwiningMap (ρ.comp φ) (σ.comp φ)) where
  toFun f := {
    toLinearMap := f.toLinearMap
    isIntertwining' p := f.isIntertwining' (φ p) }
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem representationRestrictionHom_injective {k G P V A : Type} [Field k]
    [Group G] [Group P] [AddCommGroup V] [Module k V]
    [AddCommGroup A] [Module k A]
    (ρ : Representation k G V) (σ : Representation k G A) (φ : P→*G) :
    Function.Injective (representationRestrictionHom ρ σ φ) := by
  intro f g h
  have hh := congrArg (fun z : Representation.IntertwiningMap (ρ.comp φ) (σ.comp φ) =>
    z.toLinearMap) h
  exact Representation.IntertwiningMap.ext hh

theorem representationCharacterHead_le_restriction {p : ℕ} [Fact p.Prime]
    {G P V : Type} [Group G] [Group P] [AddCommGroup V]
    [Module (ZMod p) V] [FiniteDimensional (ZMod p) V]
    (ρ : Representation (ZMod p) G V) (φ : P→*G) :
    Module.finrank (ZMod p) (primeActionCharacters p (representationGroupAction ρ))≤
      Module.finrank (ZMod p)
        (primeActionCharacters p (representationGroupAction (ρ.comp φ))) := by
  rw [(representationCharacterHeadEquiv ρ).finrank_eq,
    (representationCharacterHeadEquiv (ρ.comp φ)).finrank_eq]
  exact (representationRestrictionHom ρ (Representation.trivial (ZMod p) G (ZMod p)) φ).finrank_le_finrank_of_injective (representationRestrictionHom_injective _ _ _)

theorem induced_finiteDimensional {k G V : Type} [Field k] [Group G] [Finite G]
    [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (H : Subgroup G) (ρ : Representation k H V) :
    FiniteDimensional k (Representation.IndV H.subtype ρ) := by
  letI : Fintype G := Fintype.ofFinite G
  exact FiniteDimensional.of_injective (inducedToCoinducedEquiv H ρ).toLinearEquiv.toLinearMap
    (inducedToCoinducedEquiv H ρ).toLinearEquiv.injective

attribute [local instance] inducedMackeyComponentAddCommGroup inducedMackeyComponentModule

def inducedMackeySubmoduleCoordinate {k G V : Type} [Field k] [Group G] [Finite G]
    [AddCommGroup V] [Module k V] (H P : Subgroup G) (ρ : Representation k H V)
    [Fintype (DoubleCoset.Quotient (H:Set G) (P:Set G))]
    (M : Subrepresentation (Representation.ind H.subtype ρ))
    (q : DoubleCoset.Quotient (H:Set G) (P:Set G)) :
    Representation.IntertwiningMap (M.toRepresentation.comp P.subtype)
      (Representation.ind (inducedOrbitStabilizer H P q.out).subtype
        (inducedOrbitFibre H P ρ q.out)) where
  toLinearMap := (LinearMap.proj q).comp
    ((inducedMackeyDecomposition H P ρ).toLinearMap.comp M.toSubmodule.subtype)
  isIntertwining' p := by
    apply LinearMap.ext
    intro v
    exact inducedMackeyDecomposition_equivariant H P ρ p v.1 q

theorem inducedMackeySubmoduleCoordinate_injective
    {k G V : Type} [Field k] [Group G] [Finite G]
    [AddCommGroup V] [Module k V] (H P : Subgroup G) (ρ : Representation k H V)
    [Fintype (DoubleCoset.Quotient (H:Set G) (P:Set G))]
    (M : Subrepresentation (Representation.ind H.subtype ρ)) :
    Function.Injective (fun v q=>inducedMackeySubmoduleCoordinate H P ρ M q v) := by
  intro v w h
  apply Subtype.ext
  apply (inducedMackeyDecomposition H P ρ).injective
  exact h

/-- Actual prime-power orbit pieces and actual joint coordinate filtration.
No decomposition or submodule splitting is assumed. -/
theorem induced_primePowerOrbit_head_bound (p : ℕ) [Fact p.Prime]
    (hTracey : TraceyPrimePowerModuleInput p)
    {G V : Type} [Group G] [Finite G] [AddCommGroup V]
    [Module (ZMod p) V] [FiniteDimensional (ZMod p) V]
    (H P : Subgroup G) (hP : IsPGroup p P) (ρ : Representation (ZMod p) H V)
    [Fintype (DoubleCoset.Quotient (H:Set G) (P:Set G))]
    (M : Subrepresentation (Representation.ind H.subtype ρ))
    (j : DoubleCoset.Quotient (H:Set G) (P:Set G)→ℕ)
    (hj : ∀q,0<j q)
    (hindex : ∀q,(inducedOrbitStabilizer H P q.out).index=p^j q) :
    Module.finrank (ZMod p)
      (primeActionCharacters p (representationGroupAction M.toRepresentation))≤
        ∑q,Module.finrank (ZMod p) V*traceyPrimePowerFactor p (j q) := by
  letI := induced_finiteDimensional H ρ
  apply (representationCharacterHead_le_restriction M.toRepresentation P.subtype).trans
  apply representationCharacterHead_le_coordinates
    (fun q=>inducedMackeyComponent H P ρ q)
    (M.toRepresentation.comp P.subtype)
    (fun q=>Representation.ind (inducedOrbitStabilizer H P q.out).subtype
      (inducedOrbitFibre H P ρ q.out))
    (fun q=>Module.finrank (ZMod p) V*traceyPrimePowerFactor p (j q))
    ?_ (inducedMackeySubmoduleCoordinate H P ρ M)
    (inducedMackeySubmoduleCoordinate_injective H P ρ M)
  intro q S
  exact traceyPrimePower_head_bound p hTracey P hP
    (inducedOrbitStabilizer H P q.out) (j q) (hj q) (hindex q) V
    (inducedOrbitFibre H P ρ q.out) S

/-- The Gaussian branch for every actual ternary induced submodule.
The only external input is the explicit published prime-power module
bound. The Sylow restriction, twisted Mackey pieces, arbitrary submodule
filtration, orbit-index valuation and integer-floor sum are all proved. -/
theorem inducedTernary_gaussian_head_bound
    (hTracey : TraceyPrimePowerModuleInput 3)
    {G V : Type} [Group G] [Finite G] [AddCommGroup V]
    [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
    (H : Subgroup G) (ρ : Representation (ZMod 3) H V)
    (M : Subrepresentation (Representation.ind H.subtype ρ))
    (hk : 0<H.index.factorization 3) :
    Module.finrank (ZMod 3)
      (primeActionCharacters 3 (representationGroupAction M.toRepresentation))≤
        Module.finrank (ZMod 3) V*
          ⌊(H.index:ℝ)/Real.sqrt (Real.pi*(H.index.factorization 3:ℝ))⌋₊ := by
  let P : Sylow 3 G := Classical.choice inferInstance
  letI : Finite (DoubleCoset.Quotient (H:Set G) ((P:Subgroup G):Set G)) :=
    Finite.of_injective (inducedDoubleCosetOrbitEquiv H (P:Subgroup G))
      (inducedDoubleCosetOrbitEquiv H (P:Subgroup G)).injective
  letI : Fintype (DoubleCoset.Quotient (H:Set G) ((P:Subgroup G):Set G)) :=
    Fintype.ofFinite _
  obtain ⟨j,hj,hkj,hs⟩ := inducedMackeySylow_indices H 3 P
  exact (induced_primePowerOrbit_head_bound 3 hTracey H (P:Subgroup G)
    P.isPGroup' ρ M j (fun q=>hk.trans_le (hkj q)) hj).trans
      (traceyTernaryPrimePower_weighted_sum (Module.finrank (ZMod 3) V) j
        (H.index.factorization 3) H.index hk hkj hs)

end SymmetricSubgroupAsymptotics
