import SymmetricSubgroupAsymptotics.RepeatedOddMarkerSection
import SymmetricSubgroupAsymptotics.TernaryDiagonalQuotientCocycles
import SymmetricSubgroupAsymptotics.Non2LiftBound

/-!
# The literal ternary kernel chart over any original marker image

The group is the whole original contraction preimage of the stated image
B. Reconstructing the original A3 coordinates identifies its actual
projection kernel with the full ternary coordinate module. The conjugation
equation uses the same original element, all original signs and the entire
exterior. No splitting, finiteness or subgroup-count premise is required.
-/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics.RepeatedOddMarkerKernelChart

open RepeatedOddMarkerKernel RepeatedOddMarkerModule RepeatedOddMarkerSection

variable {ι D : Type} [Fintype ι] [Group D]
    (B : Subgroup ((ι → Multiplicative (ZMod 2)) × D))

def signCharacter (i : ι) : B →* Multiplicative (ZMod 2) where
  toFun b := b.1.1 i
  map_one' := rfl
  map_mul' _ _ := rfl

def moduleRep : Rep (ZMod 3) B :=
  Rep.of (TernaryDiagonalQuotientCocycles.diagonalRepresentation (signCharacter B))

theorem contraction_reconstruction (v : Multiplicative (ι → ZMod 3)) :
    contraction (reconstruction (D := D) v) = 1 := by
  apply Prod.ext
  · funext i
    exact (OddMarkerTernaryChart.chart (Multiplicative.ofAdd (v.toAdd i))).property
  · rfl

/-- Reconstruct a vector in the original pullback kernel. -/
def kernelMap : Multiplicative (ι → ZMod 3) →* (pullbackProjection B).ker where
  toFun v := ⟨⟨reconstruction v, by
      change contraction (reconstruction v) ∈ B
      rw [contraction_reconstruction]
      exact B.one_mem⟩, by
    apply Subtype.ext
    exact contraction_reconstruction v⟩
  map_one' := Subtype.ext (Subtype.ext reconstruction.map_one)
  map_mul' v w := Subtype.ext (Subtype.ext (reconstruction.map_mul v w))

theorem kernelMap_injective : Function.Injective (kernelMap B) := by
  intro v w h
  apply reconstruction_injective (D := D)
  exact congrArg (fun x : (pullbackProjection B).ker => x.1.1) h

theorem kernelMap_surjective : Function.Surjective (kernelMap B) := by
  intro x
  have hp : contraction x.1.1 = 1 := congrArg Subtype.val x.2
  have hs (i : ι) : oddMarkerSign (x.1.1.1 i) = 1 :=
    congrArg (fun b : (ι → Multiplicative (ZMod 2)) × D => b.1 i) hp
  have hd : x.1.1.2 = 1 := congrArg Prod.snd hp
  let v : ι → ZMod 3 := fun i =>
    (OddMarkerTernaryChart.chart.symm ⟨x.1.1.1 i,hs i⟩).toAdd
  refine ⟨Multiplicative.ofAdd v,?_⟩
  apply Subtype.ext
  apply Subtype.ext
  apply Prod.ext
  · funext i
    exact congrArg Subtype.val
      (OddMarkerTernaryChart.chart.apply_symm_apply ⟨x.1.1.1 i,hs i⟩)
  · exact hd.symm

def kernelEquiv : Multiplicative (moduleRep B) ≃* (pullbackProjection B).ker :=
  MulEquiv.ofBijective (kernelMap B) ⟨kernelMap_injective B,kernelMap_surjective B⟩

@[simp] theorem kernelEquiv_original (v : Multiplicative (moduleRep B)) :
    ((kernelEquiv B v : pullback B) : (ι → OddMarkerGroup) × D) =
      reconstruction v := rfl

/-- The exact original extension chart, ready to quotient by any literal
invariant submodule without changing the group or its quotient action. -/
def originalKernelChart : OriginalKernelModuleChart (pullbackProjection B) (moduleRep B) where
  equiv := kernelEquiv B
  conjugate q v := by
    apply Subtype.ext
    apply Prod.ext
    · funext i
      exact (OddMarkerTernaryChart.chart_conjugate_coe (q.1.1 i)
        (Multiplicative.ofAdd (v i))).symm
    · change (1 : D) = q.1.2 * 1 * q.1.2⁻¹
      simp

end SymmetricSubgroupAsymptotics.RepeatedOddMarkerKernelChart

end
