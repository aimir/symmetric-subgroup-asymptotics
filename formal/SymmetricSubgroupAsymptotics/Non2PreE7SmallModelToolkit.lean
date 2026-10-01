import SymmetricSubgroupAsymptotics.Non2PreE7SmallAdditiveTemplate
import SymmetricSubgroupAsymptotics.Non2PreE7DerivedHeadBounds

/-!
# Literal normal menus through comparator projections

An actual action `U` is identified with a model group `G`.  Suppose a family
of onto projections `π_j : G → R` to one comparator `R` covers the normal
menu: every nontrivial normal subgroup of `G` contains some `ker π_j`.  Then
every nontrivial literal quotient `U/N` is literally a quotient of `R`, and
only the trivial kernel needs a tail bound.

The typical certificate is a self-centralizing minimal normal subgroup
`V = ker π`: every nontrivial normal subgroup meets `V`, hence contains it.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics

/-- A surjection whose kernel lies in `N` identifies `U/N` with the quotient of
the target by the image of `N`. -/
def quotientEquivOfKerLe {U R : Type*} [Group U] [Group R] (π : U →* R)
    (hπ : Function.Surjective π) (N : Subgroup U) [hN : N.Normal] (h : π.ker ≤ N) :
    haveI : (N.map π).Normal := hN.map π hπ
    U ⧸ N ≃* R ⧸ N.map π := by
  haveI : (N.map π).Normal := hN.map π hπ
  let ψ : U →* R ⧸ N.map π := (QuotientGroup.mk' (N.map π)).comp π
  have hψ : Function.Surjective ψ :=
    (QuotientGroup.mk'_surjective _).comp hπ
  have hker : ψ.ker = N := by
    ext x
    simp only [ψ, MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff]
    constructor
    · rintro ⟨n, hn, hnx⟩
      have h1 : n⁻¹ * x ∈ π.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, hnx, inv_mul_cancel]
      have := N.mul_mem hn (h h1)
      simpa using this
    · intro hx
      exact ⟨x, hx, rfl⟩
  exact (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective ψ hψ)

/-- A self-centralizing minimal normal subgroup lies in every nontrivial
normal subgroup. -/
theorem le_of_minimal_selfCentralizing {G : Type*} [Group G] (V : Subgroup G)
    [hV : V.Normal]
    (hmin : ∀ W : Subgroup G, W.Normal → W ≤ V → W = ⊥ ∨ W = V)
    (hcent : ∀ x : G, (∀ v ∈ V, x * v = v * x) → x ∈ V)
    (N : Subgroup G) [hN : N.Normal] (hNb : N ≠ ⊥) : V ≤ N := by
  have hinf : (N ⊓ V).Normal := Subgroup.normal_inf_normal N V
  rcases hmin (N ⊓ V) hinf inf_le_right with h | h
  · exfalso
    apply hNb
    have hNV : N ≤ V := by
      intro x hx
      apply hcent
      intro v hv
      have hc : x * v * x⁻¹ * v⁻¹ ∈ N ⊓ V := by
        refine ⟨?_, V.mul_mem (hV.conj_mem v hv x) (V.inv_mem hv)⟩
        have h2 : v * x⁻¹ * v⁻¹ ∈ N := hN.conj_mem x⁻¹ (N.inv_mem hx) v
        have h3 : x * (v * x⁻¹ * v⁻¹) ∈ N := N.mul_mem hx h2
        simpa [mul_assoc] using h3
      rw [h] at hc
      have h1 : x * v * x⁻¹ * v⁻¹ = 1 := (Subgroup.mem_bot).mp hc
      calc x * v = (x * v * x⁻¹ * v⁻¹) * (v * x) := by group
        _ = v * x := by rw [h1, one_mul]
    rw [eq_bot_iff]
    intro x hx
    have : x ∈ N ⊓ V := ⟨hx, hNV hx⟩
    rw [h] at this
    exact this
  · rw [← h]
    exact inf_le_left

namespace Non2UnipotentPrefixFiniteMenu

/-- An actual action identified with a model group whose nontrivial normal
subgroups all contain the kernel of one of finitely many onto projections to
a single comparator. -/
structure PreE7NormalComparatorModel (w : ℕ) (i : PreE7NonPairActionClass w) : Type 1 where
  G : Type
  [groupG : Group G]
  [finiteG : Finite G]
  equiv : preE7NonPairAction w i ≃* G
  index : Type
  R : Type
  [groupR : Group R]
  [finiteR : Finite R]
  degree : ℕ
  action : R →* Equiv.Perm (Fin degree)
  action_injective : Function.Injective action
  proj : index → (G →* R)
  proj_surjective : ∀ j, Function.Surjective (proj j)
  normal_cover : ∀ N : Subgroup G, N.Normal → N ≠ ⊥ → ∃ j, (proj j).ker ≤ N
  tailSlope : ℝ
  tailConstant : ℝ
  tailConstant_nonneg : 0 ≤ tailConstant
  tail : ∀ (b : ℕ) (J : Subgroup (Equiv.Perm (Fin b))),
    (Nat.card (GroupEpimorphism J G) : ℝ) ≤ tailConstant * (2 : ℝ) ^ (tailSlope * b)
  comparator_window : preE7CharacterRho * w ≤
    ((evenWidth w : ℝ) - ((max 2 degree : ℕ) : ℝ)) / 8
  tail_window : tailSlope ≤ preE7CharacterWindow w

attribute [instance] PreE7NormalComparatorModel.groupG PreE7NormalComparatorModel.finiteG
  PreE7NormalComparatorModel.groupR PreE7NormalComparatorModel.finiteR

namespace PreE7NormalComparatorModel

variable {w : ℕ} {i : PreE7NonPairActionClass w} (M : PreE7NormalComparatorModel w i)

/-- The certificate on one literal normal axis. -/
def axis (N : {N : Subgroup (preE7NonPairAction w i) // N.Normal}) :
    PreE7SmallAxisCertificate (preE7NonPairAction w i) N M.R M.tailSlope := by
  haveI : N.1.Normal := N.2
  by_cases h : N.1 = ⊥
  · refine .tail M.tailConstant M.tailConstant_nonneg (fun b J => ?_)
    have e : (preE7NonPairAction w i ⧸ N.1) ≃* M.G :=
      (QuotientGroup.quotientMulEquivOfEq h).trans
        ((QuotientGroup.quotientBot).trans M.equiv)
    rw [fusionGroupEpimorphism_card_congr (MulEquiv.refl J) e]
    exact M.tail b J
  · let N' : Subgroup M.G := N.1.map M.equiv.toMonoidHom
    haveI hN' : N'.Normal := N.2.map _ M.equiv.surjective
    have hN'b : N' ≠ ⊥ := by
      intro hb
      apply h
      rw [eq_bot_iff]
      intro x hx
      have : M.equiv x ∈ N' := ⟨x, hx, rfl⟩
      rw [hb] at this
      have h1 : M.equiv x = 1 := (Subgroup.mem_bot).mp this
      exact (Subgroup.mem_bot).mpr (M.equiv.injective (h1.trans (map_one _).symm))
    let j := Classical.choose (M.normal_cover N' hN' hN'b)
    have hj := Classical.choose_spec (M.normal_cover N' hN' hN'b)
    haveI : (N'.map (M.proj j)).Normal := hN'.map _ (M.proj_surjective j)
    exact .comparator ⟨N'.map (M.proj j), inferInstance⟩
      ((QuotientGroup.congr N.1 N' M.equiv rfl).trans
        (quotientEquivOfKerLe (M.proj j) (M.proj_surjective j) N' hj))

/-- The small additive template data. -/
def toData : PreE7SmallAdditiveData w i where
  R := M.R
  degree := M.degree
  action := M.action
  action_injective := M.action_injective
  tailSlope := M.tailSlope
  comparator_window := M.comparator_window
  tail_window := M.tail_window
  axis := M.axis

include M in
/-- The action is accepted by the mixed local catalogue. -/
theorem localFamilyAction (family : PreE7NoPairNoC3EarlierOwnerFamily) :
    preE7NoPairNoC3EarlierLocalFamilyAction family w i :=
  M.toData.localFamilyAction family

end PreE7NormalComparatorModel

end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics
