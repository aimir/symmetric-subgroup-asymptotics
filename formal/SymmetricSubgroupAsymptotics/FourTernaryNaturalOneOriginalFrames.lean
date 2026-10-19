import SymmetricSubgroupAsymptotics.FourPointAlternatingGeneratorCover
import SymmetricSubgroupAsymptotics.ProductBlockFrameGenerators
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveTernaryAlternatingNaturalFamily
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveTernaryBlockCycleNaturalFamily
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveRow72PolynomialFamily

/-! Shared physical four-triple charts for five actual natural-one rows.
Only generator point images and two A4 generator words are checked. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.FourTernaryNaturalOneOriginalFrames
open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeTwoTwelvePairFiniteCatalogue

def generators : Fin 5 → Fin 4 → Equiv.Perm (Fin 12) :=
  ![row122Generators,row157Generators,row213Generators,row232Generators,row259Generators]
abbrev Original (r : Fin 5) := Subgroup.closure (Set.range (generators r))
def pointFrame : Fin 4 × Fin 3 ≃ Fin 12 :=
  (Equiv.prodComm (Fin 4) (Fin 3)).trans finProdFinEquiv

def tops (r : Fin 5) (j : Fin 4) : Equiv.Perm (Fin 4) where
  toFun i := ⟨(generators r j ⟨i.val,by omega⟩).val % 4,Nat.mod_lt _ (by decide)⟩
  invFun i := ⟨((generators r j)⁻¹ ⟨i.val,by omega⟩).val % 4,Nat.mod_lt _ (by decide)⟩
  left_inv := by revert r j; decide +kernel
  right_inv := by revert r j; decide +kernel
private theorem preserves : ∀ (r : Fin 5) (j : Fin 4) (z : Fin 4 × Fin 3),
    (pointFrame.symm (generators r j (pointFrame z))).1 = tops r j z.1 := by decide +kernel

def frame (r : Fin 5) : ProductBlockFrame (Original r) (Fin 4) (Fin 3) :=
  ProductBlockFrame.ofGenerators pointFrame (generators r) (tops r) (preserves r)
def originalGenerator (r : Fin 5) (j : Fin 4) : Original r :=
  ⟨generators r j,Subgroup.subset_closure (Set.mem_range_self j)⟩
private theorem top_generator (r : Fin 5) (j : Fin 4) :
    (frame r).top (originalGenerator r j) = tops r j :=
  ProductBlockFrame.ofGenerators_top_generator pointFrame (generators r) (tops r) (preserves r) j

def aWord (r : Fin 5) : Original r :=
  let t := originalGenerator r 2
  let s := originalGenerator r 3
  (![originalGenerator r 2,originalGenerator r 3,(t*s)⁻¹,
    (originalGenerator r 3)⁻¹,s*t*s*t⁻¹] : Fin 5 → Original r) r

def bWord (r : Fin 5) : Original r :=
  let t := originalGenerator r 2
  (![originalGenerator r 3,t*(aWord r)⁻¹*t⁻¹,t*(aWord r)⁻¹*t⁻¹,
    originalGenerator r 2,originalGenerator r 2] : Fin 5 → Original r) r

private theorem a_top (r : Fin 5) : (frame r).top (aWord r) =
    FourPointAlternatingGeneratorCover.a := by
  fin_cases r
  · change (frame 0).top (originalGenerator 0 2) = _
    rw [top_generator]
    decide +kernel
  · change (frame 1).top (originalGenerator 1 3) = _
    rw [top_generator]
    decide +kernel
  · change (frame 2).top ((originalGenerator 2 2 * originalGenerator 2 3)⁻¹) = _
    simp only [map_inv,map_mul,top_generator]
    decide +kernel
  · change (frame 3).top ((originalGenerator 3 3)⁻¹) = _
    simp only [map_inv,top_generator]
    decide +kernel
  · change (frame 4).top (originalGenerator 4 3 * originalGenerator 4 2 *
      originalGenerator 4 3 * (originalGenerator 4 2)⁻¹) = _
    simp only [map_mul,map_inv,top_generator]
    decide +kernel
private theorem b_top (r : Fin 5) : (frame r).top (bWord r) =
    FourPointAlternatingGeneratorCover.b := by
  fin_cases r
  · change (frame 0).top (originalGenerator 0 3) = _
    rw [top_generator]
    decide +kernel
  · change (frame 1).top (originalGenerator 1 2 * (aWord 1)⁻¹ *
      (originalGenerator 1 2)⁻¹) = _
    simp only [map_mul,map_inv,a_top,top_generator]
    decide +kernel
  · change (frame 2).top (originalGenerator 2 2 * (aWord 2)⁻¹ *
      (originalGenerator 2 2)⁻¹) = _
    simp only [map_mul,map_inv,a_top,top_generator]
    decide +kernel
  · change (frame 3).top (originalGenerator 3 2) = _
    rw [top_generator]
    decide +kernel
  · change (frame 4).top (originalGenerator 4 2) = _
    rw [top_generator]
    decide +kernel

theorem alternating_le (r : Fin 5) : alternatingGroup (Fin 4) ≤ (frame r).top.range :=
  FourPointAlternatingGeneratorCover.alternating_le _
    ⟨aWord r,a_top r⟩ ⟨bWord r,b_top r⟩

end SymmetricSubgroupAsymptotics.FourTernaryNaturalOneOriginalFrames
