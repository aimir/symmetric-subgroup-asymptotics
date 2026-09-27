import SymmetricSubgroupAsymptotics.RepeatedOddMarkerModule

/-!
# The actual binary image of the repeated-marker contraction

The source of the later cocycle count is the literal image of all original
signs and the complete exterior. Its binary property is proved separately
from the possibly nonbinary original group. Original sign equality and
kernel invariance descend through this same surjection.
-/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics.RepeatedOddMarkerImage

open RepeatedOddMarkerKernel

variable {ι D : Type*} [Group D]

def image (H : Subgroup ((ι → OddMarkerGroup) × D)) :
    Subgroup ((ι → Multiplicative (ZMod 2)) × D) := H.map contraction

def quotientMap (H : Subgroup ((ι → OddMarkerGroup) × D)) : H →* image H :=
  (contraction.comp H.subtype).codRestrict (image H)
    (fun h => Subgroup.mem_map.mpr ⟨h.1,h.2,rfl⟩)

theorem quotientMap_surjective (H : Subgroup ((ι → OddMarkerGroup) × D)) :
    Function.Surjective (quotientMap H) := by
  rintro ⟨b,hb⟩
  obtain ⟨x,hx,hxb⟩ := Subgroup.mem_map.mp hb
  exact ⟨⟨x,hx⟩,Subtype.ext hxb⟩

/-- A uniform exponent two on the sign coordinates needs no finite index
set. The exterior element supplies its own binary exponent. -/
theorem image_isPGroup (hD : IsPGroup 2 D)
    (H : Subgroup ((ι → OddMarkerGroup) × D)) : IsPGroup 2 (image H) := by
  have hambient : IsPGroup 2 ((ι → Multiplicative (ZMod 2)) × D) := by
    intro x
    obtain ⟨k,hk⟩ := hD x.2
    refine ⟨k+1,?_⟩
    apply Prod.ext
    · funext i
      change (x.1 i)^(2^(k+1))=1
      rw [pow_succ,Nat.mul_comm (2^k) 2,pow_mul,binary_mul_pow_two,one_pow]
    · change x.2^(2^(k+1))=1
      rw [pow_succ,pow_mul,hk,one_pow]
  exact hambient.to_subgroup (image H)

def signCharacter (H : Subgroup ((ι → OddMarkerGroup) × D)) (i : ι) :
    image H →* Multiplicative (ZMod 2) where
  toFun b := b.1.1 i
  map_one' := rfl
  map_mul' _ _ := rfl

theorem signCharacter_comp (H : Subgroup ((ι → OddMarkerGroup) × D)) (i : ι) :
    (signCharacter H i).comp (quotientMap H)=RepeatedOddMarkerModule.signCharacter H i := rfl

/-- The same retained signs are equal before and after the contraction. -/
theorem signCharacter_eq_iff (H : Subgroup ((ι → OddMarkerGroup) × D)) (i j : ι) :
    signCharacter H i=signCharacter H j ↔
      RepeatedOddMarkerModule.signCharacter H i=RepeatedOddMarkerModule.signCharacter H j := by
  constructor
  · intro h
    exact congrArg (fun f => f.comp (quotientMap H)) h
  · intro h
    apply MonoidHom.ext
    intro b
    obtain ⟨x,rfl⟩ := quotientMap_surjective H b
    exact DFunLike.congr_fun h x

def scalar (H : Subgroup ((ι → OddMarkerGroup) × D)) (i : ι) (b : image H) : ZMod 3 :=
  OddMarkerTernaryChart.signScalar (signCharacter H i b)

/-- Kernel invariance is now stated on the actual binary image used for
the fibre count, with the original reconstructed submodule unchanged. -/
theorem diagonal_mem (H : Subgroup ((ι → OddMarkerGroup) × D))
    (b : image H) (v : ι → ZMod 3) (hv : v ∈ RepeatedOddMarkerModule.kernelSubmodule H) :
    DiagonalIsotypeProjection.diagonalOperator (scalar H) b v ∈
      RepeatedOddMarkerModule.kernelSubmodule H := by
  obtain ⟨h,rfl⟩ := quotientMap_surjective H b
  exact RepeatedOddMarkerModule.diagonal_mem H h v hv

/-- Fullness of an original S3 coordinate gives an actual nontrivial
sign on this same binary image. -/
theorem signCharacter_nontrivial (H : Subgroup ((ι → OddMarkerGroup) × D)) (i : ι)
    (hfull : H.map (coordinate i)=⊤) :
    ∃ b : image H, signCharacter H i b ≠ 1 := by
  let g : OddMarkerGroup := Equiv.swap (0 : Fin 3) 1
  have hg : oddMarkerSign g≠1 := by
    rw [ne_eq,oddMarkerSign_eq_one]
    dsimp [g]
    rw [Equiv.Perm.sign_swap (by decide)]
    decide
  have hm : g ∈ H.map (coordinate i) := by rw [hfull]; trivial
  obtain ⟨x,hx,hxi⟩ := Subgroup.mem_map.mp hm
  refine ⟨quotientMap H ⟨x,hx⟩,?_⟩
  change oddMarkerSign (x.1 i)≠1
  change x.1 i=g at hxi
  rw [hxi]
  exact hg

end SymmetricSubgroupAsymptotics.RepeatedOddMarkerImage

end
