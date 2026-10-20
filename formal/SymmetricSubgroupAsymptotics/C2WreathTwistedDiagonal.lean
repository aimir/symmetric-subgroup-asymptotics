import SymmetricSubgroupAsymptotics.Non2PreE7C2Wreath

/-! A scalar group with a binary automorphism maps into a two-coordinate
wreath by its diagonal or twisted diagonal. The exact two coordinate maps
are retained, and the binary generator maps to the pure block swap. -/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics
namespace C2WreathTwistedDiagonal

open SemidirectProduct

abbrev Binary := Multiplicative (ZMod 2)

variable {C A : Type} [Group C] [Group A]
  (alpha : Binary →* MulAut C) (f : C →* A)

def pair : C →* A × A := f.prod (f.comp (alpha C2Wreath.gen).toMonoidHom)

theorem alpha_twice (c : C) : alpha C2Wreath.gen (alpha C2Wreath.gen c) = c := by
  change (alpha C2Wreath.gen * alpha C2Wreath.gen) c = c
  rw [← map_mul, C2Wreath.gen_mul_gen, map_one]
  rfl

def intoWreath : C ⋊[alpha] Binary →* C2Wreath.W A :=
  SemidirectProduct.map (pair alpha f) (MonoidHom.id Binary) (by
    intro b
    apply MonoidHom.ext
    intro c
    rcases C2Wreath.cases b with rfl | rfl
    · change pair alpha f (alpha 1 c) = C2Wreath.swapAut A 1 (pair alpha f c)
      rw [map_one, C2Wreath.swapAut_one]
      rfl
    · change (f (alpha C2Wreath.gen c), f (alpha C2Wreath.gen (alpha C2Wreath.gen c))) =
        C2Wreath.swapAut A C2Wreath.gen (f c, f (alpha C2Wreath.gen c))
      rw [C2Wreath.swapAut_gen, alpha_twice])

theorem intoWreath_inl (c : C) :
    intoWreath alpha f (inl c) = inl (f c, f (alpha C2Wreath.gen c)) := rfl

theorem intoWreath_inr (b : Binary) : intoWreath alpha f (inr b) = inr b := by
  apply SemidirectProduct.ext
  · change (f 1, f (alpha C2Wreath.gen 1)) = 1
    simp only [map_one]
    rfl
  · rfl

end C2WreathTwistedDiagonal
end SymmetricSubgroupAsymptotics

end
