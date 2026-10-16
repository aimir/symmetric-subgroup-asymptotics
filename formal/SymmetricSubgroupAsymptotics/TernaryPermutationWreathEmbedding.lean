import SymmetricSubgroupAsymptotics.TernarySignedPermutationSubgroupSocles
import SymmetricSubgroupAsymptotics.OddMarkerTernaryChart
import SymmetricSubgroupAsymptotics.PermutationalWreathProduct

/-! The literal permutations of three points embed in ternary affine
coordinates. Applied coordinatewise, this embeds every actual subgroup
of the three-point local wreath into the signed ternary model, retaining
its complete block projection. Uniform normal bounds are pulled back
through this actual image. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.TernaryPermutationWreathEmbedding

open SemidirectProduct

abbrev Local := Equiv.Perm (Fin 3)

def label (i : Fin 3) : ZMod 3 := i.val
def offset (g : Local) : ZMod 3 := label (g 0)

theorem label_injective : Function.Injective label := by decide +kernel

theorem local_affine : ∀ (g : Local) (i : Fin 3),
    label (g i) = offset g +
      BinarySignTernaryLinear.coefficient (oddMarkerSign g).toAdd * label i := by
  decide +kernel

theorem local_injective (g h : Local) (ho : offset g = offset h)
    (hs : oddMarkerSign g = oddMarkerSign h) : g = h := by
  apply Equiv.ext
  intro i
  apply label_injective
  rw [local_affine,local_affine,ho,hs]

theorem offset_mul (g h : Local) : offset (g*h) = offset g +
    BinarySignTernaryLinear.coefficient (oddMarkerSign g).toAdd * offset h :=
  local_affine g (h 0)

variable {R I : Type} [Group R] [MulAction R I] [Fintype I] [DecidableEq I]

abbrev W := PermutationalWreathProduct Local R I
abbrev signs : Subrepresentation
    (CyclicOrbitBinarySignNormalGenerators.permutationRepresentation (R := R) (X := I)) := ⊤
abbrev Target := TernarySignedPermutationSubgroupSocles.Model (signs (R := R) (I := I))

def signMap : W (R := R) (I := I) →*
    TernarySignedPermutationSubgroupSocles.SignModel (signs (R := R) (I := I)) where
  toFun g := ⟨Multiplicative.ofAdd ⟨fun i => (oddMarkerSign (g.left i)).toAdd,
    Submodule.mem_top⟩,g.right⟩
  map_one' := by
    apply SemidirectProduct.ext
    · apply Multiplicative.toAdd.injective
      apply Subtype.ext
      funext i
      change (oddMarkerSign 1).toAdd = 0
      rw [map_one]
      rfl
    · rfl
  map_mul' g h := by
    apply SemidirectProduct.ext
    · apply Multiplicative.toAdd.injective
      apply Subtype.ext
      funext i
      change (oddMarkerSign (g.left i * h.left (g.right⁻¹ • i))).toAdd =
        (oddMarkerSign (g.left i)).toAdd + (oddMarkerSign (h.left (g.right⁻¹ • i))).toAdd
      rw [map_mul]
      rfl
    · rfl

def affine : W (R := R) (I := I) →* Target (R := R) (I := I) where
  toFun g := ⟨Multiplicative.ofAdd (fun i => offset (g.left i)),signMap g⟩
  map_one' := by
    apply SemidirectProduct.ext
    · apply Multiplicative.toAdd.injective
      funext i
      rfl
    · exact signMap.map_one
  map_mul' g h := by
    apply SemidirectProduct.ext
    · apply Multiplicative.toAdd.injective
      funext i
      exact offset_mul (g.left i) (h.left (g.right⁻¹ • i))
    · exact signMap.map_mul g h

theorem affine_injective : Function.Injective (affine (R := R) (I := I)) := by
  intro g h he
  apply PermutationalWreathProduct.ext
  · funext i
    apply local_injective
    · exact congrArg (fun z : Target (R := R) (I := I) => z.left.toAdd i) he
    · apply Multiplicative.toAdd.injective
      exact congrArg (fun z : Target (R := R) (I := I) => z.right.left.toAdd.val i) he
  · exact congrArg (fun z : Target (R := R) (I := I) => z.right.right) he

variable [Finite R]

instance : Finite (W (R := R) (I := I)) :=
  Finite.of_injective (fun g : W (R := R) (I := I) => (g.left,g.right))
    (fun _ _ h => PermutationalWreathProduct.ext (congrArg Prod.fst h) (congrArg Prod.snd h))

theorem normal_generating_tuples (C : Subgroup (W (R := R) (I := I)))
    (hsurj : Function.Surjective
      ((PermutationalWreathProduct.rightHom : W (R := R) (I := I) →* R).comp C.subtype))
    (c : R) (i : I) (hcycle : ∀ j : I, ∃ n : ℕ, c^n • i = j)
    (a : ℕ) (ha : ∀ N : Subgroup R, N.Normal → MarkedC4.normalGen N ≤ a) :
    ∀ N : Subgroup C, N.Normal →
      ∃ x : Fin (2+a) → C, Subgroup.normalClosure (Set.range x) = N := by
  let f : C →* Target (R := R) (I := I) := affine.comp C.subtype
  let J := f.range
  let e : C ≃* J := MulEquiv.ofBijective f.rangeRestrict
    ⟨fun _ _ h => (affine_injective.comp Subtype.val_injective)
      (congrArg Subtype.val h),f.rangeRestrict_surjective⟩
  have hb : Function.Surjective (TernarySignedPermutationSubgroupSocles.blocks signs J) := by
    intro r
    obtain ⟨g,hg⟩ := hsurj r
    refine ⟨(LinearSemidirectSubgroupKernelChart.projection
      (TernarySignedPermutationSubgroupSocles.linearAction signs) J).rangeRestrict
        (f.rangeRestrict g),?_⟩
    exact hg
  exact normal_generating_tuples_of_surjective e.symm.toMonoidHom e.symm.surjective
    (TernarySignedPermutationSubgroupSocles.normal_generating_tuples signs J c i hcycle hb a ha)

end SymmetricSubgroupAsymptotics.TernaryPermutationWreathEmbedding

end
