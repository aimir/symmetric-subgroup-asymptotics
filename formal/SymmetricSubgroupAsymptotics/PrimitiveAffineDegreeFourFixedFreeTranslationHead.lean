import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeFourPairFrameSource
import SymmetricSubgroupAsymptotics.BinaryConjugateTripleRelativeHead
import Mathlib.Tactic.Abel

/-! The fixed-free branch of the dynamic four-by-four frame. All normal
subgroups and characters remain in the original action group. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer

variable {w : ℕ} {U : PreE7NonPairActionClass w} {basePoint : Fin w}
    (block : OriginalMinimalBlock (A := preE7NonPairAction w U) basePoint)
    (P : PrimitiveAffineProfile block.Component block.Fibre)
    [Nontrivial block.Fibre]

local instance fixedFreeTranslationHead_profilePrimeFact : Fact P.p.Prime := (chart block P).primeFact
local instance fixedFreeTranslationHead_binaryPrimeFact : Fact (Nat.Prime 2) := ⟨by decide⟩

/-- A fixed-free order-three action on the actual translation module
annihilates the relative binary head of every literal intersection E∩N. -/
theorem degreeFour_fixedFree_translation_intersection_head_zero
    (hp : P.p = 2)
    (g : preE7NonPairAction w U)
    (hg : (QuotientGroup.mk' (E block P) g) ^ 3 = 1)
    (hfixed : ∀ v : (elementaryChart block P).V,
      (elementaryChart block P).quotientRepresentation.ρ
        (QuotientGroup.mk' (E block P) g) v = v → v = 0)
    (N : Subgroup (preE7NonPairAction w U)) [N.Normal] :
    Module.finrank (ZMod 2) (primeRelativeCharacters 2 (E block P ⊓ N)) = 0 := by
  let C := elementaryChart block P
  let q := QuotientGroup.mk' (E block P) g
  let c : C.V →ₗ[ZMod C.p] C.V := C.quotientRepresentation.ρ q
  have hc (v : C.V) : c (c (c v)) = v := by
    change (C.quotientRepresentation.ρ q ^ 3) v = v
    rw [← map_pow, hg, map_one]
    rfl
  have htrace (v : C.V) : v + c v + c (c v) = 0 := by
    apply hfixed
    change c (v + c v + c (c v)) = v + c v + c (c v)
    simp only [map_add, hc]
    abel
  apply binary_relativeHead_eq_zero_of_conjugate_triple (E block P ⊓ N) g
  intro n
  let e : E block P := ⟨n, n.2.1⟩
  have he : e * MulAut.conjNormal g e *
      MulAut.conjNormal g (MulAut.conjNormal g e) = 1 := by
    apply C.equiv.injective
    apply Multiplicative.toAdd.injective
    simp only [map_mul, map_one]
    change (C.equiv e).toAdd + (C.equiv (MulAut.conjNormal g e)).toAdd +
      (C.equiv (MulAut.conjNormal g (MulAut.conjNormal g e))).toAdd = 0
    rw [← C.quotientRepresentation_apply g (MulAut.conjNormal g e),
      ← C.quotientRepresentation_apply g e]
    exact htrace ((C.equiv e).toAdd)
  apply Subtype.ext
  exact congrArg (fun x : E block P => (x : preE7NonPairAction w U)) he

end Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
end SymmetricSubgroupAsymptotics
