import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairedEightAffineLiteralTops
import SymmetricSubgroupAsymptotics.Non2PreE7AffineModel
import SymmetricSubgroupAsymptotics.BinaryBitmaskCoordinates

/-!
# Literal binary affine coordinates for paired-eight rows 18 and 20

The original point labels are the ordinary three-bit masks. The retained
seven-cycle is linear in these coordinates, the shared involution is a
translation, and the extra row-20 generator swaps two coordinates. Seven
conjugates supply every nonzero translation, so the literal closures are
the full affine groups of their generated linear subgroups.

The finite reductions below concern at most three-bit vectors and the
eight original points. No group-cardinality or normal-subgroup enumeration
is used. Simplicity of the row-20 linear subgroup is a separate certificate.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics
namespace PrimitiveAffineDegreeTwoPairedEightAffineTops

open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer

abbrev Vector := AffineModel.V 2 3
abbrev LinearGroup := AffineModel.GLV 2 3

/-- The original point label is the binary mask, least significant bit first. -/
def pointEquiv : Vector ≃ Fin 8 where
  toFun v := ⟨binaryVectorMask v, by decide +kernel +revert⟩
  invFun i := binaryVectorOfMask 3 i.val
  left_inv := by decide +kernel
  right_inv := by decide +kernel

/-- The retained seven-cycle, written as a linear map. -/
def singer : LinearGroup where
  toFun v := ![v 1, v 0 + v 2, v 0]
  invFun v := ![v 2, v 0, v 1 + v 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel
  map_add' := by decide +kernel
  map_smul' := by decide +kernel

/-- The extra row-20 generator interchanges the two low coordinates. -/
def swap : LinearGroup where
  toFun v := ![v 1, v 0, v 2]
  invFun v := ![v 1, v 0, v 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel
  map_add' := by decide +kernel
  map_smul' := by decide +kernel

def firstVector : Vector := binaryVectorOfMask 3 1

def linearAction : LinearGroup →* Equiv.Perm Vector where
  toFun g := g.toEquiv
  map_one' := rfl
  map_mul' _ _ := rfl

/-- Linear maps acting on the retained eight point labels. -/
def linearPerm : LinearGroup →* Equiv.Perm (Fin 8) :=
  pointEquiv.permCongrHom.toMonoidHom.comp linearAction

theorem linearPerm_injective : Function.Injective linearPerm := by
  intro g h hgh
  have hact : linearAction g = linearAction h :=
    pointEquiv.permCongrHom.injective hgh
  apply LinearEquiv.ext
  intro v
  exact congrArg (fun q : Equiv.Perm Vector ↦ q v) hact

/-- Vector addition acting on the retained eight point labels. -/
def translationPerm : Multiplicative Vector →* Equiv.Perm (Fin 8) :=
  pointEquiv.permCongrHom.toMonoidHom.comp AffineModel.transl

theorem linearPerm_singer :
    linearPerm singer = DegreeTwoPairedEightSharedTops.top18Generators 0 := by
  ext x
  revert x
  decide +kernel

theorem linearPerm_swap :
    linearPerm swap = DegreeTwoPairedEightSharedTops.top20Generators 1 := by
  ext x
  revert x
  decide +kernel

theorem translationPerm_firstVector :
    translationPerm (Multiplicative.ofAdd firstVector) =
      DegreeTwoPairedEightSharedTops.top18Generators 1 := by
  ext x
  revert x
  decide +kernel

/-- The singer cycle is transitive on all seven nonzero vectors. -/
theorem singer_nonzero_orbit : ∀ x y : Vector, x ≠ 0 → y ≠ 0 →
    ∃ i : Fin 7, (singer ^ i.val) x = y := by
  decide +kernel

/-- Any linear subgroup containing the retained singer acts irreducibly. -/
theorem irreducible_of_singer_mem (R : Subgroup LinearGroup) (ha : singer ∈ R) :
    AffineModel.Irreducible R := by
  intro S hS
  by_cases hbot : S = ⊥
  · exact Or.inl hbot
  right
  have hx : ∃ x ∈ S, x ≠ 0 := by
    by_contra h
    push Not at h
    apply hbot
    apply le_antisymm _ bot_le
    intro x hx
    exact AddSubgroup.mem_bot.mpr (h x hx)
  obtain ⟨x, hx, hx0⟩ := hx
  apply top_unique
  intro y _hy
  by_cases hy0 : y = 0
  · simpa only [hy0] using S.zero_mem
  obtain ⟨i, hi⟩ := singer_nonzero_orbit x y hx0 hy0
  rw [← hi]
  exact hS (singer ^ i.val) (R.pow_mem ha i.val) x hx

private def translationExponent (i : Fin 8) : Fin 7 :=
  (#[0, 0, 6, 2, 5, 4, 1, 3] : Array (Fin 7))[i.val]!

/-- A literal word in the original row-18 generators for each translation. -/
def translationWord (v : Vector) : Equiv.Perm (Fin 8) :=
  if v = 0 then 1 else
    DegreeTwoPairedEightSharedTops.top18Generators 0 ^
        (translationExponent (pointEquiv v)).val *
      DegreeTwoPairedEightSharedTops.top18Generators 1 *
      (DegreeTwoPairedEightSharedTops.top18Generators 0 ^
        (translationExponent (pointEquiv v)).val)⁻¹

theorem translationWord_eq (v : Vector) :
    translationWord v = translationPerm (Multiplicative.ofAdd v) := by
  ext x
  revert v x
  decide +kernel

theorem translation_mem_top18 (v : Multiplicative Vector) :
    translationPerm v ∈ DegreeTwoPairedEightSharedTops.Top18 := by
  have ha : DegreeTwoPairedEightSharedTops.top18Generators 0 ∈
      DegreeTwoPairedEightSharedTops.Top18 :=
    Subgroup.subset_closure (Set.mem_range_self 0)
  have ht : DegreeTwoPairedEightSharedTops.top18Generators 1 ∈
      DegreeTwoPairedEightSharedTops.Top18 :=
    Subgroup.subset_closure (Set.mem_range_self 1)
  change translationPerm (Multiplicative.ofAdd (Multiplicative.toAdd v)) ∈
    DegreeTwoPairedEightSharedTops.Top18
  rw [← translationWord_eq (Multiplicative.toAdd v)]
  unfold translationWord
  split
  · exact Subgroup.one_mem _
  · exact Subgroup.mul_mem _
      (Subgroup.mul_mem _ (Subgroup.pow_mem _ ha _) ht)
      (Subgroup.inv_mem _ (Subgroup.pow_mem _ ha _))

theorem top18_le_top20 :
    DegreeTwoPairedEightSharedTops.Top18 ≤ DegreeTwoPairedEightSharedTops.Top20 := by
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨i, rfl⟩
  fin_cases i
  · exact Subgroup.subset_closure ⟨0, rfl⟩
  · exact Subgroup.subset_closure ⟨2, rfl⟩

theorem translation_mem_top20 (v : Multiplicative Vector) :
    translationPerm v ∈ DegreeTwoPairedEightSharedTops.Top20 :=
  top18_le_top20 (translation_mem_top18 v)

/-- The faithful abstract affine action on the original labels. -/
def affineAction (R : Subgroup LinearGroup) :
    AffineModel.Aff R →* Equiv.Perm (Fin 8) :=
  pointEquiv.permCongrHom.toMonoidHom.comp (AffineModel.action R)

theorem affineAction_injective (R : Subgroup LinearGroup) :
    Function.Injective (affineAction R) :=
  pointEquiv.permCongrHom.injective.comp (AffineModel.action_injective R)

theorem affineAction_inl (R : Subgroup LinearGroup) (v : Multiplicative Vector) :
    affineAction R (SemidirectProduct.inl v) = translationPerm v := by
  ext x
  rfl

theorem affineAction_inr (R : Subgroup LinearGroup) (r : R) :
    affineAction R (SemidirectProduct.inr r) = linearPerm r.1 := by
  apply Equiv.ext
  intro x
  change pointEquiv (0 + r.1 (pointEquiv.symm x)) =
    pointEquiv (r.1 (pointEquiv.symm x))
  rw [zero_add]

/-- Checking linear generators suffices for their whole generated subgroup. -/
theorem linearPerm_mem_of_generators {I : Type} (g : I → LinearGroup)
    (H : Subgroup (Equiv.Perm (Fin 8))) (hg : ∀ i, linearPerm (g i) ∈ H)
    {r : LinearGroup} (hr : r ∈ Subgroup.closure (Set.range g)) :
    linearPerm r ∈ H := by
  induction hr using Subgroup.closure_induction with
  | mem r hr => obtain ⟨i, rfl⟩ := hr; exact hg i
  | one => simpa only [map_one] using H.one_mem
  | mul r s _ _ hr hs => simpa only [map_mul] using H.mul_mem hr hs
  | inv r _ hr => simpa only [map_inv] using H.inv_mem hr

/-- A certificate for the literal generated linear permutations transports
directly to the abstract linear subgroup used by `AffineModel`. -/
def linearClosureEquiv {I : Type} (g : I → LinearGroup) :
    Subgroup.closure (Set.range g) ≃*
      Subgroup.closure (Set.range (fun i ↦ linearPerm (g i))) := by
  let R := Subgroup.closure (Set.range g)
  let H := Subgroup.closure (Set.range (fun i ↦ linearPerm (g i)))
  let f : R →* Equiv.Perm (Fin 8) := linearPerm.comp R.subtype
  have hf : Function.Injective f :=
    linearPerm_injective.comp Subtype.val_injective
  have hrange : f.range = H := by
    apply le_antisymm
    · rintro _ ⟨r, rfl⟩
      exact linearPerm_mem_of_generators g H
        (fun i ↦ Subgroup.subset_closure (Set.mem_range_self i)) r.2
    · apply (Subgroup.closure_le _).mpr
      rintro _ ⟨i, rfl⟩
      exact ⟨⟨g i, Subgroup.subset_closure (Set.mem_range_self i)⟩, rfl⟩
  exact (MonoidHom.ofInjective hf).trans (MulEquiv.subgroupCongr hrange)

/-- Translations and the linear subgroup exhaust the abstract affine action. -/
theorem affineAction_range_le (R : Subgroup LinearGroup)
    (H : Subgroup (Equiv.Perm (Fin 8)))
    (htranslation : ∀ v, translationPerm v ∈ H)
    (hlinear : ∀ r ∈ R, linearPerm r ∈ H) :
    (affineAction R).range ≤ H := by
  rintro _ ⟨g, rfl⟩
  rw [← SemidirectProduct.inl_left_mul_inr_right g, map_mul,
    affineAction_inl, affineAction_inr]
  exact H.mul_mem (htranslation g.left) (hlinear g.right.1 g.right.2)

namespace Row18

abbrev Source := DegreeTwoPairedEightSharedTops.Top18
abbrev group : Group Source := inferInstance
def generators := DegreeTwoPairedEightSharedTops.top18Generators
abbrev Top : Subgroup (Equiv.Perm (Fin 8)) := Subgroup.closure (Set.range generators)
def originalEquiv : Source ≃* Top := MulEquiv.refl Source
def ambient (i : Fin 2) : Source :=
  ⟨generators i, Subgroup.subset_closure (Set.mem_range_self i)⟩

theorem ambient_full : Subgroup.closure (Set.range ambient) = ⊤ := by
  apply top_unique
  rintro ⟨x, hx⟩ htop
  clear htop
  induction hx using Subgroup.closure_induction with
  | mem y hy => obtain ⟨i, rfl⟩ := hy; exact Subgroup.subset_closure ⟨i, rfl⟩
  | one => exact Subgroup.one_mem _
  | mul x y _ _ hx hy => exact Subgroup.mul_mem _ hx hy
  | inv x _ hx => exact Subgroup.inv_mem _ hx

def linearGenerators : Fin 1 → LinearGroup := fun _ ↦ singer
abbrev linearGroup : Subgroup LinearGroup := Subgroup.closure (Set.range linearGenerators)

def linearTopGenerators : Fin 1 → Equiv.Perm (Fin 8) :=
  fun i ↦ linearPerm (linearGenerators i)

abbrev linearTop : Subgroup (Equiv.Perm (Fin 8)) :=
  Subgroup.closure (Set.range linearTopGenerators)

theorem linearTopGenerators_eq (i : Fin 1) :
    linearTopGenerators i = DegreeTwoPairedEightSharedTops.top18Generators 0 :=
  linearPerm_singer

def linearTopEquiv : linearGroup ≃* linearTop :=
  linearClosureEquiv linearGenerators

theorem singer_mem : singer ∈ linearGroup :=
  Subgroup.subset_closure ⟨0, rfl⟩

theorem irreducible : AffineModel.Irreducible linearGroup :=
  irreducible_of_singer_mem linearGroup singer_mem

theorem affineAction_range : (affineAction linearGroup).range = Top := by
  apply le_antisymm
  · apply affineAction_range_le linearGroup Top translation_mem_top18
    intro r hr
    exact linearPerm_mem_of_generators linearGenerators Top
      (fun i ↦ by
        rw [show linearGenerators i = singer from rfl, linearPerm_singer]
        exact Subgroup.subset_closure (Set.mem_range_self 0)) hr
  · apply (Subgroup.closure_le _).mpr
    rintro _ ⟨i, rfl⟩
    fin_cases i
    · exact ⟨SemidirectProduct.inr (⟨singer, singer_mem⟩ : linearGroup),
        (affineAction_inr _ _).trans linearPerm_singer⟩
    · exact ⟨SemidirectProduct.inl (Multiplicative.ofAdd firstVector),
        (affineAction_inl _ _).trans translationPerm_firstVector⟩

/-- The retained literal permutation group is the displayed abstract affine group. -/
def modelEquiv : Top ≃* AffineModel.Aff linearGroup :=
  (MulEquiv.subgroupCongr affineAction_range.symm).trans
    (MonoidHom.ofInjective (affineAction_injective linearGroup)).symm

end Row18

namespace Row20

abbrev Source := DegreeTwoPairedEightSharedTops.Top20
abbrev group : Group Source := inferInstance
def generators := DegreeTwoPairedEightSharedTops.top20Generators
abbrev Top : Subgroup (Equiv.Perm (Fin 8)) := Subgroup.closure (Set.range generators)
def originalEquiv : Source ≃* Top := MulEquiv.refl Source
def ambient (i : Fin 3) : Source :=
  ⟨generators i, Subgroup.subset_closure (Set.mem_range_self i)⟩

theorem ambient_full : Subgroup.closure (Set.range ambient) = ⊤ := by
  apply top_unique
  rintro ⟨x, hx⟩ htop
  clear htop
  induction hx using Subgroup.closure_induction with
  | mem y hy => obtain ⟨i, rfl⟩ := hy; exact Subgroup.subset_closure ⟨i, rfl⟩
  | one => exact Subgroup.one_mem _
  | mul x y _ _ hx hy => exact Subgroup.mul_mem _ hx hy
  | inv x _ hx => exact Subgroup.inv_mem _ hx

def linearGenerators : Fin 2 → LinearGroup := ![singer, swap]
abbrev linearGroup : Subgroup LinearGroup := Subgroup.closure (Set.range linearGenerators)

def linearTopGenerators : Fin 2 → Equiv.Perm (Fin 8) :=
  fun i ↦ linearPerm (linearGenerators i)

abbrev linearTop : Subgroup (Equiv.Perm (Fin 8)) :=
  Subgroup.closure (Set.range linearTopGenerators)

theorem linearTopGenerators_eq (i : Fin 2) :
    linearTopGenerators i =
      ![DegreeTwoPairedEightSharedTops.top20Generators 0,
        DegreeTwoPairedEightSharedTops.top20Generators 1] i := by
  fin_cases i
  · exact linearPerm_singer
  · exact linearPerm_swap

def linearTopEquiv : linearGroup ≃* linearTop :=
  linearClosureEquiv linearGenerators

theorem singer_mem : singer ∈ linearGroup :=
  Subgroup.subset_closure ⟨0, rfl⟩

theorem swap_mem : swap ∈ linearGroup :=
  Subgroup.subset_closure ⟨1, rfl⟩

theorem irreducible : AffineModel.Irreducible linearGroup :=
  irreducible_of_singer_mem linearGroup singer_mem

theorem affineAction_range : (affineAction linearGroup).range = Top := by
  apply le_antisymm
  · apply affineAction_range_le linearGroup Top translation_mem_top20
    intro r hr
    apply linearPerm_mem_of_generators linearGenerators Top _ hr
    intro i
    fin_cases i
    · change linearPerm singer ∈ Top
      rw [linearPerm_singer]
      exact Subgroup.subset_closure ⟨0, rfl⟩
    · change linearPerm swap ∈ Top
      rw [linearPerm_swap]
      exact Subgroup.subset_closure (Set.mem_range_self 1)
  · apply (Subgroup.closure_le _).mpr
    rintro _ ⟨i, rfl⟩
    fin_cases i
    · exact ⟨SemidirectProduct.inr (⟨singer, singer_mem⟩ : linearGroup),
        (affineAction_inr _ _).trans linearPerm_singer⟩
    · exact ⟨SemidirectProduct.inr (⟨swap, swap_mem⟩ : linearGroup),
        (affineAction_inr _ _).trans linearPerm_swap⟩
    · exact ⟨SemidirectProduct.inl (Multiplicative.ofAdd firstVector),
        (affineAction_inl _ _).trans translationPerm_firstVector⟩

/-- The retained literal permutation group is the displayed abstract affine group. -/
def modelEquiv : Top ≃* AffineModel.Aff linearGroup :=
  (MulEquiv.subgroupCongr affineAction_range.symm).trans
    (MonoidHom.ofInjective (affineAction_injective linearGroup)).symm

end Row20

end PrimitiveAffineDegreeTwoPairedEightAffineTops
end SymmetricSubgroupAsymptotics

end
