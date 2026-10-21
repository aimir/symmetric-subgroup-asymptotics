import Mathlib.GroupTheory.PGroup
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Group.TypeTags.Finite
import Mathlib.Data.Fin.VecNotation

/-! Every automorphism of C4×C2 has eighth power one. Only64 possible
generator-image pairs and eight maps on eight points are checked. No full
function-space or subgroup census is used. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.FourByTwoAutomorphismBinary

abbrev Model := Multiplicative (ZMod 4 × ZMod 2)
def a : Model := Multiplicative.ofAdd (1,0)
def b : Model := Multiplicative.ofAdd (0,1)

def normalMap (u v : Model) (x : Model) : Model :=
  u ^ x.toAdd.1.val * v ^ x.toAdd.2.val

theorem normal_form (x : Model) : x = normalMap a b x := by
  have h : ∀ x : Model,x = normalMap a b x := by decide +kernel
  exact h x

def maps (i : Fin 8) : Model → Model :=
  normalMap
    (Multiplicative.ofAdd ((![1,3,1,3,1,3,1,3] : Fin 8 → ZMod 4) i,
      (![0,0,1,1,0,0,1,1] : Fin 8 → ZMod 2) i))
    (Multiplicative.ofAdd ((![0,0,0,0,2,2,2,2] : Fin 8 → ZMod 4) i,1))

set_option maxHeartbeats 1000000 in
private theorem image_pair_cases : ∀ (u v : Model),v ^ 2 = 1 →
    Function.Injective (normalMap u v) → ∃ i : Fin 8,normalMap u v = maps i := by
  decide +kernel

set_option maxHeartbeats 1000000 in
private theorem maps_eighth : ∀ (i : Fin 8) (x : Model),(maps i)^[8] x = x := by
  decide +kernel

theorem automorphism_eighth (f : MulAut Model) : f ^ 8 = 1 := by
  have hf : (f : Model → Model) = normalMap (f a) (f b) := by
    funext x
    change f x = f a ^ x.toAdd.1.val * f b ^ x.toAdd.2.val
    rw [←map_pow,←map_pow,←map_mul]
    exact congrArg f (normal_form x)
  have hb : (f b)^2 = 1 := by
    rw [←map_pow,show b^2=1 from by decide +kernel,map_one]
  have hinj : Function.Injective (normalMap (f a) (f b)) := hf ▸ f.injective
  obtain ⟨i,hi⟩ := image_pair_cases (f a) (f b) hb hinj
  apply MulEquiv.ext
  intro x
  change (f^[8]) x = x
  rw [hf,hi]
  exact maps_eighth i x

theorem automorphisms_isPGroup : IsPGroup 2 (MulAut Model) :=
  fun f => ⟨3,automorphism_eighth f⟩

end SymmetricSubgroupAsymptotics.FourByTwoAutomorphismBinary
end
