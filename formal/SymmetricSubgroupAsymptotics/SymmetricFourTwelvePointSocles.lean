import SymmetricSubgroupAsymptotics.GeneratedLiteralImage
import SymmetricSubgroupAsymptotics.NaturalFourNormalChains

/-! The six-edge action of the literal symmetric group, together with its
sign coordinate.  The resulting twelve-point action is defined by a group
homomorphism, not by an enumerated twelve-point group.  Any generating-tuple
binding of this action inherits the normal chain of the original `S₄`,
simultaneously for every literal normal denominator. -/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics.SymmetricFourTwelvePointSocles

abbrev Group := Equiv.Perm (Fin 4)
abbrev Point := Fin 6 × Fin 2

def ends : Fin 6 → Fin 4 × Fin 4 :=
  ![(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)]

def index (a b : Fin 4) : Fin 6 :=
  if (a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 0) then 0
  else if (a = 0 ∧ b = 2) ∨ (a = 2 ∧ b = 0) then 1
  else if (a = 0 ∧ b = 3) ∨ (a = 3 ∧ b = 0) then 2
  else if (a = 1 ∧ b = 2) ∨ (a = 2 ∧ b = 1) then 3
  else if (a = 1 ∧ b = 3) ∨ (a = 3 ∧ b = 1) then 4
  else 5

def edgeFun (g : Group) (i : Fin 6) : Fin 6 := index (g (ends i).1) (g (ends i).2)

theorem edgeFun_one : ∀ i, edgeFun 1 i = i := by decide +kernel

theorem edgeFun_mul : ∀ g h : Group, ∀ i,
    edgeFun (g * h) i = edgeFun g (edgeFun h i) := by decide +kernel

def edgePerm (g : Group) : Equiv.Perm (Fin 6) where
  toFun := edgeFun g
  invFun := edgeFun g⁻¹
  left_inv i := by rw [← edgeFun_mul, inv_mul_cancel, edgeFun_one]
  right_inv i := by rw [← edgeFun_mul, mul_inv_cancel, edgeFun_one]

def edge : Group →* Equiv.Perm (Fin 6) where
  toFun := edgePerm
  map_one' := Equiv.ext edgeFun_one
  map_mul' g h := Equiv.ext (edgeFun_mul g h)

def binarySign : Group →* Equiv.Perm (Fin 2) where
  toFun g := if Equiv.Perm.sign g = 1 then 1 else Equiv.swap 0 1
  map_one' := by simp
  map_mul' g h := by
    simp only [map_mul]
    rcases Int.units_eq_one_or (Equiv.Perm.sign g) with hg | hg <;>
      rcases Int.units_eq_one_or (Equiv.Perm.sign h) with hh | hh <;>
      simp [hg, hh, Equiv.swap_mul_self]

def edgeSign : Group →* Equiv.Perm Point where
  toFun g := Equiv.prodCongr (edge g) (binarySign g)
  map_one' := by
    apply Equiv.ext
    intro x
    apply Prod.ext <;> simp
  map_mul' g h := by
    apply Equiv.ext
    intro x
    apply Prod.ext <;> simp [Equiv.prodCongr_apply, Equiv.Perm.mul_apply]

def literalAction (points : Point ≃ Fin 12) : Group →* Equiv.Perm (Fin 12) :=
  points.permCongrHom.toMonoidHom.comp edgeSign

def generators : Fin 3 → Group :=
  ![Equiv.swap 0 1 * Equiv.swap 2 3,
    Equiv.swap 0 1 * Equiv.swap 1 2,
    Equiv.swap 1 2]

theorem generates : Subgroup.closure (Set.range generators) = ⊤ := by
  let K := Subgroup.closure (Set.range generators)
  have member (i : Fin 3) : generators i ∈ K :=
    Subgroup.subset_closure (Set.mem_range_self i)
  have hc : finRotate 4 ∈ K := by
    have h := K.mul_mem (K.mul_mem (member 2) (member 1)) (member 0)
    have he : generators 2 * generators 1 * generators 0 = finRotate 4 := by decide +kernel
    rwa [he] at h
  have hs : Equiv.swap (0 : Fin 4) 1 ∈ K := by
    have h := K.mul_mem (member 1) (member 2)
    have he : generators 1 * generators 2 = Equiv.swap 0 1 := by decide +kernel
    rwa [he] at h
  have hgen : Subgroup.closure
      ({finRotate 4, Equiv.swap (0 : Fin 4) 1} : Set Group) = ⊤ := by
    simpa only [show finRotate 4 (0 : Fin 4) = 1 from rfl] using
      Equiv.Perm.closure_cycle_adjacent_swap
        (isCycle_finRotate_of_le (by decide : 2 ≤ 4))
        (support_finRotate_of_le (by decide : 2 ≤ 4)) (0 : Fin 4)
  apply top_unique
  rw [← hgen]
  apply (Subgroup.closure_le K).mpr
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl
  · exact hc
  · exact hs

/-- An exact point binding to the displayed generating tuple gives the
one-generator socle bound in every quotient of the original image group. -/
theorem quotientSocle {n : ℕ} (points : Point ≃ Fin 12)
    (source : Fin n → Group) (target : Fin n → Equiv.Perm (Fin 12))
    (hsource : Subgroup.closure (Set.range source) = ⊤)
    (hbinding : ∀ i, literalAction points (source i) = target i)
    (N : Subgroup (Subgroup.closure (Set.range target))) [N.Normal] :
    SocleNormalGeneratorBound (Subgroup.closure (Set.range target) ⧸ N) 1 := by
  let q := GeneratedLiteralImage.toTop (literalAction points) source target
    (Equiv.refl _) hsource (by simpa using hbinding)
  have hq : Function.Surjective q := GeneratedLiteralImage.toTop_surjective
    (literalAction points) source target (Equiv.refl _) hsource (by simpa using hbinding)
  exact quotientSocleNormalGeneratorBound_one_of_normal_total
    (normalSubgroups_total_of_surjective q hq NaturalFourNormalChains.symmetric_normal_total) N

end SymmetricSubgroupAsymptotics.SymmetricFourTwelvePointSocles

end
