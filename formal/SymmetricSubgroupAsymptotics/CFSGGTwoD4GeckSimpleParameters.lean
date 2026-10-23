import SymmetricSubgroupAsymptotics.CFSGGTwoD4GeckOrbitRootGroups
import SymmetricSubgroupAsymptotics.CFSGTrialityGeckSignedSimpleParameters
import SymmetricSubgroupAsymptotics.CFSGTrialityGeckRootGeneratedPGroup

/-! Uniform K-parameter homomorphisms for the four actual signed
identity-twist simple groups. Bool false denotes the outer orbit and
Bool true the middle node. Both parameter maps are proved injective. -/
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGGTwoD4GeckSimpleParameters
open CFSGTrialityD4NormTwo CFSGTrialityGeckDiagramCovariance
open CFSGTrialityGeckFixedOrbitRootGroups CFSGTrialityGeckSimpleChartWeyl
open CFSGTrialityGeckFixedRootWords CFSGTrialityGeckShortOrbitCommutator
open CFSGTrialityGeckSimpleOrbitFlags CFSGTrialityGeckRelativeRootGenerated
open CFSGTrialityGeckShortCentralizerCardinality CFSGTrialityGeckRootGeneratedPGroup
open CFSGTrialityGeckRootSubgroupTwist CFSGTrialityGeckMatrixTwist CFSGSerreQuadraticMatrix
open CFSGSerreQuadraticWeylWord
variable (K : Type) [Field K] [Finite K]

def middleRawHom (isNegative : Bool) : Multiplicative K →* (Matrix GeckIndex GeckIndex K)ˣ where
  toFun t := canonicalRoot rawData K isNegative 1 t.toAdd
  map_one' := canonicalRoot_zero rawData K isNegative 1
  map_mul' t u := (canonicalRoot_add rawData K isNegative 1 t.toAdd u.toAdd).symm

def simpleRawHom (isNegative a : Bool) : Multiplicative K →* (Matrix GeckIndex GeckIndex K)ˣ :=
  if a then middleRawHom K isNegative else shortOrbitHom K (RingEquiv.refl K) isNegative

def simpleGeneratedHom (isNegative a : Bool) :
    Multiplicative K →* fixedRootGenerated K (RingEquiv.refl K) :=
  (simpleRawHom K isNegative a).codRestrict _ (fun t => by
    cases a
    · exact shortOrbit_mem_generated K (RingEquiv.refl K) isNegative t.toAdd rfl
    · exact central_root_mem_generated K (RingEquiv.refl K) isNegative t.toAdd rfl)

theorem simpleGeneratedHom_val (isNegative a : Bool) (t : Multiplicative K) :
    (simpleGeneratedHom K isNegative a t).val =
      if a then canonicalRoot rawData K isNegative 1 t.toAdd
      else shortOrbit K (RingEquiv.refl K) isNegative t.toAdd := by
  cases a <;> rfl

theorem simpleGeneratedHom_mem_rootPart (isNegative a : Bool) (t : Multiplicative K) :
    simpleGeneratedHom K isNegative a t ∈ rootPart K (RingEquiv.refl K) isNegative := by
  cases a
  · exact ⟨shortOrbit_mem_rootGroup K (RingEquiv.refl K) isNegative t.toAdd,
      shortOrbit_fixed K (RingEquiv.refl K) isNegative t.toAdd rfl⟩
  · refine ⟨Subgroup.subset_closure ⟨(1, t.toAdd), rfl⟩, ?_⟩
    change unitTwist K (RingEquiv.refl K) (canonicalRoot rawData K isNegative 1 t.toAdd) =
      canonicalRoot rawData K isNegative 1 t.toAdd
    rw [unitTwist_raw_root]
    rfl

private theorem negative_parameter_injective {R G : Type*} [AddGroup R] [Group G]
    (e : MulAut G) (x y : R → G) (he : ∀ t, e (x t) = y (-t))
    (hx : Function.Injective x) : Function.Injective y := by
  intro t u htu
  have hneg : x (-t) = x (-u) := by
    apply e.injective
    calc
      e (x (-t)) = y t := by simpa only [neg_neg] using he (-t)
      _ = y u := htu
      _ = e (x (-u)) := by simpa only [neg_neg] using (he (-u)).symm
  exact neg_injective (hx hneg)

theorem simpleGeneratedHom_injective (isNegative a : Bool) :
    Function.Injective (simpleGeneratedHom K isNegative a) := by
  have hraw : Function.Injective (fun t : K =>
      if a then canonicalRoot rawData K isNegative 1 t
      else shortOrbit K (RingEquiv.refl K) isNegative t) := by
    cases isNegative
    · cases a
      · exact shortOrbit_injective K (RingEquiv.refl K)
      · exact canonical_middle_injective K
    · apply negative_parameter_injective
        (MulAut.conj (canonicalWord rawData K (orbitWord a)))
        (fun t => if a then canonicalRoot rawData K false 1 t
          else shortOrbit K (RingEquiv.refl K) false t)
        (fun t => if a then canonicalRoot rawData K true 1 t
          else shortOrbit K (RingEquiv.refl K) true t)
      · intro t
        cases a
        · exact short_word_conjugates K (RingEquiv.refl K) t
        · exact middle_word_conjugates K t
      · cases a
        · exact shortOrbit_injective K (RingEquiv.refl K)
        · exact canonical_middle_injective K
  intro t u he
  apply (Multiplicative.toAdd : Multiplicative K ≃ K).injective
  apply hraw
  simpa only [simpleGeneratedHom_val] using congrArg Subtype.val he

end SymmetricSubgroupAsymptotics.CFSGGTwoD4GeckSimpleParameters
