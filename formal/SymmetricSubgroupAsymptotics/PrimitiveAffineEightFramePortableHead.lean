import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameGeneratedTopTable
import SymmetricSubgroupAsymptotics.RepresentationIntertwinerGenerators
import SymmetricSubgroupAsymptotics.RepresentationSectionSubrepresentationHead

/-!
Portable use of an existing generated eight-frame row. Its retained
Schreier representatives and generator matrices give an injection of the
actual coinduced representation into the certified coordinate module.
This theorem has no enclosing affine profile or physical block hypothesis,
so the same checked row can also be used by the sixteen-point pair branch.
It does not assert that any literal certificate has a standard axiom audit;
that obligation remains with each concrete instance supplied to this API.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
namespace GeneratedRowData

variable (T : GeneratedTopData) (R : GeneratedRowData T)

abbrev sourceLocalRepresentation :
    Representation (ZMod 2) T.sourceStabilizer (Fin 2 → ZMod 2) :=
  R.localRepresentation.comp R.sourceLocalMap

abbrev coindCoordinates :
    Representation.coindV T.sourceStabilizer.subtype
      (R.sourceLocalRepresentation T) →ₗ[ZMod 2] (Fin 16 → ZMod 2) :=
  CoinducedLeadingCoordinates.coordinates T.sourceStabilizer
    (R.sourceLocalRepresentation T) T.representative (Pi.basisFun (ZMod 2) (Fin 2))

theorem coindCoordinates_label
    (v : Representation.coindV T.sourceStabilizer.subtype
      (R.sourceLocalRepresentation T)) (a : Fin 8) (i : Fin 2) :
    R.coindCoordinates T v (CoinducedLeadingCoordinates.label a i) =
      v.1 (T.representative a) i := by
  have h := CoinducedLeadingCoordinates.coordinates_label T.sourceStabilizer
    (R.sourceLocalRepresentation T) T.representative
    (Pi.basisFun (ZMod 2) (Fin 2)) v a i
  simpa only [Pi.basisFun_equivFun, LinearEquiv.refl_apply] using h

theorem coindCoordinates_generator
    (j : T.GeneratorIndex)
    (v : Representation.coindV T.sourceStabilizer.subtype
      (R.sourceLocalRepresentation T)) :
    R.coindCoordinates T
        (Representation.coind T.sourceStabilizer.subtype
          (R.sourceLocalRepresentation T) (T.ambient j) v) =
      R.modelRepresentation (T.ambient j) (R.coindCoordinates T v) := by
  funext z
  obtain ⟨⟨a, i⟩, rfl⟩ := (finProdFinEquiv (m := 8) (n := 2)).surjective z
  change R.coindCoordinates T _ (CoinducedLeadingCoordinates.label a i) =
    R.modelRepresentation (T.ambient j) (R.coindCoordinates T v)
      (CoinducedLeadingCoordinates.label a i)
  rw [R.modelRepresentation_generator_formula]
  have hrow : (fun q => R.coindCoordinates T v
      (CoinducedLeadingCoordinates.label (T.next j a) q)) =
      v.1 (T.representative (T.next j a)) := by
    funext q
    exact R.coindCoordinates_label T v (T.next j a) q
  rw [hrow]
  rw [R.coindCoordinates_label]
  change v.1 (T.representative a * T.ambient j) i =
    R.localRepresentation (R.sourceLocalMap (T.twist j a))
      (v.1 (T.representative (T.next j a))) i
  rw [T.representative_mul_generator]
  exact congrFun (v.2 (T.twist j a) (T.representative (T.next j a))) i

/-- Same source coinduced functions, mapped to the retained literal rows. -/
def coindEmbedding :
    (Representation.coind T.sourceStabilizer.subtype
      (R.sourceLocalRepresentation T)).IntertwiningMap R.modelRepresentation :=
  representationIntertwiningMap_of_generators _ _ (R.coindCoordinates T)
    T.ambient T.ambient_full (R.coindCoordinates_generator T)

theorem coindEmbedding_injective : Function.Injective (R.coindEmbedding T) :=
  CoinducedLeadingCoordinates.coordinates_injective T.sourceStabilizer
    (R.sourceLocalRepresentation T) T.representative
    (Pi.basisFun (ZMod 2) (Fin 2)) T.representative_factor

/-- The finite module registry controls every subrepresentation of the
original row's coinduced model, without constructing a fictitious profile. -/
theorem coind_head_le_two
    (B : Subrepresentation (Representation.coind T.sourceStabilizer.subtype
      (R.sourceLocalRepresentation T))) :
    Module.finrank (ZMod 2)
      (B.toRepresentation.IntertwiningMap
        (Representation.trivial (ZMod 2) T.ModelGroup (ZMod 2))) ≤ 2 := by
  classical
  letI : Fintype T.ModelGroup := Fintype.ofFinite T.ModelGroup
  letI : FiniteDimensional (ZMod 2)
      (Representation.coindV T.sourceStabilizer.subtype (R.sourceLocalRepresentation T)) :=
    FiniteDimensional.of_injective
      (Representation.coindV T.sourceStabilizer.subtype (R.sourceLocalRepresentation T)).subtype
      (Representation.coindV T.sourceStabilizer.subtype
        (R.sourceLocalRepresentation T)).subtype_injective
  apply uniformSubrepresentationHeadBound_of_injective
    (Representation.coind T.sourceStabilizer.subtype (R.sourceLocalRepresentation T))
    R.modelRepresentation (R.coindEmbedding T) (R.coindEmbedding_injective T) 2 _ B
  intro A
  letI : FiniteDimensional (ZMod 2) A.toSubmodule :=
    FiniteDimensional.of_injective A.toSubmodule.subtype A.toSubmodule.subtype_injective
  rw [representationHead_finrank_eq_coinvariants]
  exact R.moduleRegistry.toHeadRegistry.bound A

/-- An exact change of local binary plane preserves the portable bound. -/
theorem coind_head_le_two_of_local_equiv
    {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V]
    (rho : Representation (ZMod 2) T.sourceStabilizer V)
    (e : rho.Equiv (R.sourceLocalRepresentation T))
    (B : Subrepresentation (Representation.coind T.sourceStabilizer.subtype rho)) :
    Module.finrank (ZMod 2)
      (B.toRepresentation.IntertwiningMap
        (Representation.trivial (ZMod 2) T.ModelGroup (ZMod 2))) ≤ 2 := by
  classical
  letI : Fintype T.ModelGroup := Fintype.ofFinite T.ModelGroup
  letI : FiniteDimensional (ZMod 2)
      (Representation.coindV T.sourceStabilizer.subtype rho) :=
    FiniteDimensional.of_injective
      (Representation.coindV T.sourceStabilizer.subtype rho).subtype
      (Representation.coindV T.sourceStabilizer.subtype rho).subtype_injective
  let j := (R.coindEmbedding T).comp
    (Representation.coindMap T.sourceStabilizer.subtype e.toIntertwiningMap)
  have hj : Function.Injective j := by
    intro f g hfg
    change (R.coindEmbedding T)
        (Representation.coindMap T.sourceStabilizer.subtype e.toIntertwiningMap f) =
      (R.coindEmbedding T)
        (Representation.coindMap T.sourceStabilizer.subtype e.toIntertwiningMap g) at hfg
    have h := R.coindEmbedding_injective T hfg
    apply Subtype.ext
    funext x
    apply e.injective
    exact congrArg
      (fun f : Representation.coindV T.sourceStabilizer.subtype
        (R.sourceLocalRepresentation T) => f.1 x) h
  apply uniformSubrepresentationHeadBound_of_injective
    (Representation.coind T.sourceStabilizer.subtype rho)
    R.modelRepresentation j hj 2 _ B
  intro A
  letI : FiniteDimensional (ZMod 2) A.toSubmodule :=
    FiniteDimensional.of_injective A.toSubmodule.subtype A.toSubmodule.subtype_injective
  rw [representationHead_finrank_eq_coinvariants]
  exact R.moduleRegistry.toHeadRegistry.bound A

end GeneratedRowData
end Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
end SymmetricSubgroupAsymptotics

end
