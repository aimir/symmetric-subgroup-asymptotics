import SymmetricSubgroupAsymptotics.CFSGOuterCardinalityAlignment

/-! Inner alignment bounds Out by an aligned subgroup index. Counting
an inner subgroup in a two-step stabilizer tower needs no injectivity of
its original group parameters and no normality of the counted subgroup. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOuterAlignedIndex
open PrimitiveSocleRawStructure
variable {G : Type} [Group G] [Finite G]

theorem outer_card_le_aligned_index (S : Subgroup (MulAut G)) (R : Subgroup S)
    (halign : ∀ f : MulAut G, ∃ g : G, MulAut.conj g * f ∈ S)
    (hinner : ∀ r : R, (r.val : MulAut G) ∈ Inner G) :
    Nat.card (Outer G) ≤ R.index := by
  letI : Finite (MulAut G) := Finite.of_injective
    (fun f : MulAut G => (f : G → G)) DFunLike.coe_injective
  let out : MulAut G →* Outer G := QuotientGroup.mk' (Inner G)
  let q : S →* Outer G := out.comp S.subtype
  have hsurj : Function.Surjective q := by
    intro o
    obtain ⟨f, hf⟩ := QuotientGroup.mk'_surjective (Inner G) o
    obtain ⟨g, hg⟩ := halign f
    refine ⟨⟨MulAut.conj g * f, hg⟩, ?_⟩
    change out (MulAut.conj g * f) = o
    have hkill : out (MulAut.conj g) = 1 :=
      (QuotientGroup.eq_one_iff _).mpr ⟨g, rfl⟩
    rw [map_mul, hkill, one_mul]
    exact hf
  have hR : R ≤ q.ker := by
    intro r hr
    change out (r : MulAut G) = 1
    exact (QuotientGroup.eq_one_iff _).mpr (hinner ⟨r, hr⟩)
  have hcard : q.ker.index = Nat.card (Outer G) := by
    rw [Subgroup.index_eq_card]
    exact Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective q hsurj).toEquiv
  rw [← hcard]
  apply Nat.le_of_dvd
  · rw [Subgroup.index_eq_card]
    exact Nat.card_pos
  · exact Subgroup.index_dvd_of_le hR

theorem outer_card_le_aligned_tower (S : Subgroup (MulAut G))
    (A : Subgroup S) (R : Subgroup A)
    (halign : ∀ f : MulAut G, ∃ g : G, MulAut.conj g * f ∈ S)
    (hinner : ∀ r : R, (r.val.val : MulAut G) ∈ Inner G)
    (a b : ℕ) (hA : A.index ≤ a) (hR : R.index ≤ b) :
    Nat.card (Outer G) ≤ b * a := by
  have h := outer_card_le_aligned_index S (R.map A.subtype) halign (by
    rintro ⟨r, ⟨x, hx, he⟩⟩
    have hi := hinner ⟨x, hx⟩
    have he' : (x.val : MulAut G) = (r : MulAut G) := congrArg S.subtype he
    exact he' ▸ hi)
  rw [Subgroup.index_map_subtype] at h
  exact h.trans (Nat.mul_le_mul hR hA)

end SymmetricSubgroupAsymptotics.CFSGOuterAlignedIndex
