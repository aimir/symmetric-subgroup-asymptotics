import SymmetricSubgroupAsymptotics.CyclicSocleQuotientTools
import SymmetricSubgroupAsymptotics.CyclicQuotientSocles
import SymmetricSubgroupAsymptotics.BinaryPlaneSurjectiveImage
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeSixS3WreathSource
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairTowerCyclicPrefix

/-!
# Small quotient endpoints for the two paired-six models

Nontrivial normal kernels are detected by short commutator words. The
remaining quotients factor through a binary plane; the plane embedding is
obtained by a linear section, with no subgroup enumeration.
-/

set_option autoImplicit false
set_option maxRecDepth 8192
noncomputable section
open scoped Classical commutatorElement

namespace SymmetricSubgroupAsymptotics
namespace PairedSixSmallQuotientAlternatives

open CyclicSocleQuotientTools
open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeTwoPairTowerCyclicPrefix

abbrev S3 := Equiv.Perm (Fin 3)
abbrev C2 := Multiplicative (ZMod 2)
abbrev Plane := BinaryPlaneSurjectiveImage.Plane

def rotation : S3 := Equiv.swap (0 : Fin 3) 1 * Equiv.swap (1 : Fin 3) 2
def bit : C2 := Multiplicative.ofAdd 1

theorem comm_mem_normal {G : Type} [Group G] (N : Subgroup G) (hN : N.Normal)
    {x : G} (hx : x ∈ N) (g : G) : ⁅g, x⁆ ∈ N := by
  rw [commutatorElement_def]
  exact N.mul_mem (hN.conj_mem _ hx g) (N.inv_mem hx)

theorem s3_kernel_form (a : S3) (ha : oddMarkerSign a = 1) :
    ∃ i : Fin 3, rotation ^ i.val = a := by
  revert a
  decide +kernel

theorem s3_commutator_word (a : S3) (ha : a ≠ 1) :
    ∃ s : S3, ⁅s, a⁆ = rotation ∨ ⁅s, a⁆⁻¹ = rotation := by
  revert a
  decide +kernel

theorem s3_normal_cover (N : Subgroup S3) (hN : N.Normal) (hne : N ≠ ⊥) :
    oddMarkerSign.ker ≤ N := by
  obtain ⟨a, ha, hane⟩ := N.bot_or_exists_ne_one.resolve_left hne
  obtain ⟨s, hs | hs⟩ := s3_commutator_word a hane
  all_goals
    have hc := comm_mem_normal N hN ha s
    have hr : rotation ∈ N := by
      first | exact hs ▸ hc | exact hs ▸ N.inv_mem hc
    intro x hx
    obtain ⟨i, hi⟩ := s3_kernel_form x hx
    rw [← hi]
    exact N.pow_mem hr i.val

theorem s3_socle : SocleNormalGeneratorBound S3 1 := by
  apply socleBound_of_normal_cover oddMarkerSign.ker _ s3_normal_cover
  intro hbot
  have hr : rotation ∈ oddMarkerSign.ker := by decide +kernel
  have hne : rotation ≠ 1 := by decide +kernel
  exact hne (Subgroup.mem_bot.mp (hbot ▸ hr))

theorem socle_of_cyclic {G : Type} [Group G] [IsCyclic G] :
    SocleNormalGeneratorBound G 1 :=
  normal_generating_singletons_of_isCyclic (finiteGroupSocle G) inferInstance

theorem s3_image_socle {Q : Type} [Group Q]
    (q : S3 →* Q) (hq : Function.Surjective q) : SocleNormalGeneratorBound Q 1 := by
  by_cases hbot : q.ker = ⊥
  · exact socleBound_equiv (MulEquiv.ofBijective q
      ⟨(MonoidHom.ker_eq_bot_iff q).mp hbot, hq⟩) s3_socle
  · obtain ⟨f, hf, _⟩ := exists_surjective_factor oddMarkerSign
      oddMarkerSign_surjective q hq (s3_normal_cover q.ker inferInstance hbot)
    letI : IsCyclic Q := isCyclic_of_surjective f hf
    exact socle_of_cyclic

private theorem socle_of_cyclic_supergroup {G : Type} [Group G]
    (K : Subgroup G) [IsCyclic K] (hK : finiteGroupSocle G ≤ K) :
    SocleNormalGeneratorBound G 1 := by
  letI : IsCyclic (finiteGroupSocle G) := Subgroup.isCyclic_of_le hK
  obtain ⟨g, hg⟩ := (finiteGroupSocle G).isCyclic_iff_exists_zpowers_eq_top.mp
    (inferInstance : IsCyclic (finiteGroupSocle G))
  refine ⟨fun _ : Fin 1 ↦ g, ?_⟩
  have hrange : Set.range (fun _ : Fin 1 ↦ g) = {g} := by ext x; simp
  rw [hrange]
  apply le_antisymm
  · apply Subgroup.normalClosure_le_normal
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst x
    rw [← hg]
    exact Subgroup.mem_zpowers g
  · rw [← hg, Subgroup.zpowers_eq_closure]
    exact Subgroup.closure_le_normalClosure

def pairToPlane : C2 × C2 →* Plane where
  toFun x := ![x.1, x.2]
  map_one' := by funext i; fin_cases i <;> rfl
  map_mul' x y := by funext i; fin_cases i <;> rfl

theorem pairToPlane_surjective : Function.Surjective pairToPlane := by
  intro x
  refine ⟨(x 0, x 1), ?_⟩
  funext i
  fin_cases i <;> simp [pairToPlane]

theorem pairToPlane_injective : Function.Injective pairToPlane := by
  intro x y h
  exact Prod.ext (by simpa [pairToPlane] using congrFun h 0)
    (by simpa [pairToPlane] using congrFun h 1)

namespace S3Binary

abbrev G := S3 × C2

def projection : G →* Plane :=
  pairToPlane.comp (oddMarkerSign.prodMap (MonoidHom.id C2))

theorem projection_surjective : Function.Surjective projection := by
  intro x
  obtain ⟨a, ha⟩ := oddMarkerSign_surjective (x 0)
  refine ⟨(a, x 1), ?_⟩
  funext i
  fin_cases i
  · simpa [projection, pairToPlane] using ha
  · simp [projection, pairToPlane]

theorem mem_projection_ker (x : G) :
    x ∈ projection.ker ↔ oddMarkerSign x.1 = 1 ∧ x.2 = 1 := by
  change pairToPlane (oddMarkerSign x.1, x.2) = 1 ↔ _
  constructor
  · intro h
    have hp : (oddMarkerSign x.1, x.2) = 1 :=
      pairToPlane_injective (h.trans pairToPlane.map_one.symm)
    exact ⟨congrArg Prod.fst hp, congrArg Prod.snd hp⟩
  · rintro ⟨h1, h2⟩
    rw [h1, h2]
    exact pairToPlane.map_one

theorem core_le_of_first_ne (N : Subgroup G) (hN : N.Normal)
    (a : G) (ha : a ∈ N) (hne : a.1 ≠ 1) : projection.ker ≤ N := by
  obtain ⟨s, hs | hs⟩ := s3_commutator_word a.1 hne
  all_goals
    have hc := comm_mem_normal N hN ha (s, 1)
    have hcomm : ⁅(s, (1 : C2)), a⁆ = (⁅s, a.1⁆, 1) := by
      apply Prod.ext
      · rfl
      · simp [commutatorElement_def]
    rw [hcomm] at hc
    have hr : (rotation, 1) ∈ N := by
      first
      | exact hs ▸ hc
      | have hi : (⁅s, a.1⁆⁻¹, (1 : C2)⁻¹) ∈ N := N.inv_mem hc
        simpa only [inv_one, hs] using hi
    intro x hx
    obtain ⟨hfirst, hsecond⟩ := (mem_projection_ker x).mp hx
    obtain ⟨i, hi⟩ := s3_kernel_form x.1 hfirst
    have heq : (rotation, (1 : C2)) ^ i.val = x := by
      apply Prod.ext
      · exact hi
      · simpa using hsecond.symm
    rw [← heq]
    exact N.pow_mem hr i.val

theorem normal_axis (N : Subgroup G) (hN : N.Normal) :
    projection.ker ≤ N ∨ N ≤ (MonoidHom.fst S3 C2).ker := by
  by_cases h : projection.ker ≤ N
  · exact Or.inl h
  right
  intro x hx
  change x.1 = 1
  by_contra hne
  exact h (core_le_of_first_ne N hN x hx hne)

def cyclicCarrier : Subgroup G :=
  (oddMarkerSign.comp (MonoidHom.fst S3 C2)).ker

instance cyclicCarrier_normal : cyclicCarrier.Normal := MonoidHom.normal_ker _

private theorem cyclicCarrier_isCyclic : IsCyclic cyclicCarrier := by
  apply cyclicCarrier.isCyclic_iff_exists_zpowers_eq_top.mpr
  refine ⟨(rotation, bit), le_antisymm ?_ ?_⟩
  · apply Subgroup.zpowers_le.mpr
    change oddMarkerSign rotation = 1
    decide +kernel
  · have hform : ∀ x : G, oddMarkerSign x.1 = 1 →
        ∃ i : Fin 6, (rotation, bit) ^ i.val = x := by decide +kernel
    intro x hx
    obtain ⟨i, hi⟩ := hform x hx
    rw [← hi]
    exact Subgroup.npow_mem_zpowers (rotation, bit) i.val

theorem socle : SocleNormalGeneratorBound G 1 := by
  letI := cyclicCarrier_isCyclic
  apply socle_of_cyclic_supergroup cyclicCarrier
  apply Subgroup.normalClosure_le_normal
  rintro x ⟨N, hN, hx⟩
  rcases normal_axis N hN.1 with hcore | hcentral
  · have hne : projection.ker ≠ ⊥ := by
      intro hb
      have hr : (rotation, 1) ∈ projection.ker := by
        rw [mem_projection_ker]; decide +kernel
      have hrne : (rotation, (1 : C2)) ≠ 1 := by decide +kernel
      exact hrne (Subgroup.mem_bot.mp (hb ▸ hr))
    have heq : projection.ker = N := hN.2.2 _ inferInstance hne hcore
    exact ((mem_projection_ker x).mp (heq.symm ▸ hx)).1
  · have heq : x.1 = 1 := hcentral hx
    change oddMarkerSign x.1 = 1
    rw [heq, map_one]

theorem image_alternative {Q : Type} [Group Q]
    (q : G →* Q) (hq : Function.Surjective q) : TopAlternative Q := by
  rcases normal_axis q.ker inferInstance with hcore | hcentral
  · obtain ⟨f, hf, _⟩ := exists_surjective_factor projection projection_surjective q hq hcore
    exact Or.inr (BinaryPlaneSurjectiveImage.exists_injective f hf)
  · by_cases hbot : q.ker = ⊥
    · exact Or.inl (socleBound_equiv (MulEquiv.ofBijective q
        ⟨(MonoidHom.ker_eq_bot_iff q).mp hbot, hq⟩) socle)
    · have hfull : (MonoidHom.fst S3 C2).ker ≤ q.ker := by
        obtain ⟨a, ha, hane⟩ := q.ker.bot_or_exists_ne_one.resolve_left hbot
        have ha1 : a.1 = 1 := hcentral ha
        have ha2 : a.2 = bit := by
          rcases C2Wreath.cases a.2 with h | h
          · exact (hane (Prod.ext ha1 h)).elim
          · exact h
        have hae : a = (1, bit) := Prod.ext ha1 ha2
        have hb : (1, bit) ∈ q.ker := hae ▸ ha
        intro x hx
        have hx1 : x.1 = 1 := hx
        rcases C2Wreath.cases x.2 with h | h
        · have heq : x = 1 := Prod.ext hx1 h
          rw [heq]
          exact q.ker.one_mem
        · have heq : x = (1, bit) := Prod.ext hx1 h
          rw [heq]
          exact hb
      obtain ⟨f, hf, _⟩ := exists_surjective_factor (MonoidHom.fst S3 C2)
        Prod.fst_surjective q hq hfull
      exact Or.inl (s3_image_socle f hf)

end S3Binary

namespace DihedralEight

abbrev G := DegreeSixS3Wreath.D8

private theorem eq_iff (x y : G) :
    x = y ↔ x.left = y.left ∧ x.right = y.right :=
  ⟨fun h ↦ ⟨congrArg SemidirectProduct.left h, congrArg SemidirectProduct.right h⟩,
    fun h ↦ SemidirectProduct.ext h.1 h.2⟩

def projection : G →* Plane where
  toFun x := ![x.left.1 * x.left.2, x.right]
  map_one' := by funext i; fin_cases i <;> rfl
  map_mul' := by decide +kernel

theorem projection_surjective : Function.Surjective projection := by
  intro x
  refine ⟨⟨(x 0, 1), x 1⟩, ?_⟩
  change ![x 0 * 1, x 1] = x
  funext i
  fin_cases i <;> simp

def centralBit : G := SemidirectProduct.inl (bit, bit)

private theorem kernel_form (x : G) (hx : x ∈ projection.ker) :
    x = 1 ∨ x = centralBit := by
  revert x
  simp only [eq_iff]
  decide +kernel

private theorem commutator_word (x : G) (hx : x ≠ 1) :
    x = centralBit ∨ ∃ s : G, ⁅s, x⁆ = centralBit := by
  revert x
  simp only [eq_iff]
  decide +kernel

theorem normal_cover (N : Subgroup G) (hN : N.Normal) (hne : N ≠ ⊥) :
    projection.ker ≤ N := by
  obtain ⟨x, hx, hxne⟩ := N.bot_or_exists_ne_one.resolve_left hne
  have hz : centralBit ∈ N := by
    rcases commutator_word x hxne with h | ⟨s, hs⟩
    · exact h ▸ hx
    · exact hs ▸ comm_mem_normal N hN hx s
  intro y hy
  rcases kernel_form y hy with rfl | rfl
  · exact N.one_mem
  · exact hz

theorem socle : SocleNormalGeneratorBound G 1 := by
  apply socleBound_of_normal_cover projection.ker _ normal_cover
  intro hbot
  have hz : centralBit ∈ projection.ker := by decide +kernel
  have hne : centralBit ≠ 1 := by decide +kernel
  exact hne (Subgroup.mem_bot.mp (hbot ▸ hz))

theorem image_alternative {Q : Type} [Group Q]
    (q : G →* Q) (hq : Function.Surjective q) : TopAlternative Q := by
  by_cases hbot : q.ker = ⊥
  · exact Or.inl (socleBound_equiv (MulEquiv.ofBijective q
      ⟨(MonoidHom.ker_eq_bot_iff q).mp hbot, hq⟩) socle)
  · obtain ⟨f, hf, _⟩ := exists_surjective_factor projection projection_surjective
      q hq (normal_cover q.ker inferInstance hbot)
    exact Or.inr (BinaryPlaneSurjectiveImage.exists_injective f hf)

end DihedralEight

end PairedSixSmallQuotientAlternatives
end SymmetricSubgroupAsymptotics

end
