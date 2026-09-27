import SymmetricSubgroupAsymptotics.SectionSubgroups
import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# Exact fixed-kernel fibres through the original quotient

An original subgroup with full image under π and intersection N with ker π
corresponds exactly to a section subgroup after quotienting by that same N.
The inverse is the literal preimage of the literal range of a section.
Neither a splitting, a finite ambient group, nor a quotient automorphism
factor is assumed. If an original section exists, the already checked
same-source cocycle equivalence supplies the exact fibre cardinality.
-/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics

variable {Q B : Type*} [Group Q] [Group B]

/-- Full original image and exact original kernel intersection. -/
abbrev FixedKernelSubgroupFibre (π : Q →* B) (N : Subgroup Q) :=
  {H : Subgroup Q // H.map π = ⊤ ∧ H ⊓ π.ker = N}

namespace FixedKernelSubgroupFibre

variable (π : Q →* B) (N : Subgroup Q) [N.Normal] (hN : N ≤ π.ker)

abbrev quotientProjection : Q ⧸ N →* B := QuotientGroup.lift N π hN

theorem kernel_le (H : FixedKernelSubgroupFibre π N) : N ≤ H.1 := by
  exact H.2.2.ge.trans inf_le_left

/-- Quotient exactly the original intersection, retaining the original
target B and its actual restricted projection. -/
def code (H : FixedKernelSubgroupFibre π N) : SectionSubgroup (quotientProjection π N hN) :=
  ⟨H.1.map (QuotientGroup.mk' N), by
    constructor
    · apply (injective_iff_map_eq_one _).mpr
      intro x hx
      obtain ⟨g, hg, hqg⟩ := Subgroup.mem_map.mp x.2
      have hp : π g = 1 := by
        change quotientProjection π N hN (QuotientGroup.mk' N g) = 1
        rw [hqg]
        exact hx
      have hgn : g ∈ N := by
        rw [← H.2.2]
        exact ⟨hg, hp⟩
      apply Subtype.ext
      exact hqg.symm.trans ((QuotientGroup.eq_one_iff g).mpr hgn)
    · intro b
      have hb : b ∈ H.1.map π := by rw [H.2.1]; trivial
      obtain ⟨g, hg, hgb⟩ := Subgroup.mem_map.mp hb
      exact ⟨⟨QuotientGroup.mk' N g, ⟨g, hg, rfl⟩⟩, hgb⟩⟩

/-- Decode in the original group by literal quotient preimage. -/
def decode (L : SectionSubgroup (quotientProjection π N hN)) :
    FixedKernelSubgroupFibre π N :=
  ⟨L.1.comap (QuotientGroup.mk' N), by
    constructor
    · apply top_unique
      intro b _
      obtain ⟨q, hqb⟩ := L.2.surjective b
      obtain ⟨g, hg⟩ := QuotientGroup.mk'_surjective N q.1
      apply Subgroup.mem_map.mpr
      refine ⟨g, ?_, ?_⟩
      · change QuotientGroup.mk' N g ∈ L.1
        rw [hg]
        exact q.2
      · calc
          π g = quotientProjection π N hN (QuotientGroup.mk' N g) := rfl
          _ = quotientProjection π N hN q.1 := congrArg (quotientProjection π N hN) hg
          _ = b := hqb
    · ext g
      constructor
      · rintro ⟨hg, hp⟩
        have hq : (⟨QuotientGroup.mk' N g, hg⟩ : L.1) = 1 := by
          apply L.2.injective
          change quotientProjection π N hN (QuotientGroup.mk' N g) =
            quotientProjection π N hN 1
          rw [map_one]
          exact hp
        exact (QuotientGroup.eq_one_iff g).mp (congrArg Subtype.val hq)
      · intro hg
        refine ⟨?_, hN hg⟩
        change QuotientGroup.mk' N g ∈ L.1
        have hgq : QuotientGroup.mk' N g = 1 := (QuotientGroup.eq_one_iff g).mpr hg
        rw [hgq]
        exact L.1.one_mem⟩

@[simp] theorem code_val (H : FixedKernelSubgroupFibre π N) :
    (code π N hN H).1 = H.1.map (QuotientGroup.mk' N) := rfl

@[simp] theorem decode_val (L : SectionSubgroup (quotientProjection π N hN)) :
    (decode π N hN L).1 = L.1.comap (QuotientGroup.mk' N) := rfl

@[simp] theorem decode_code (H : FixedKernelSubgroupFibre π N) :
    decode π N hN (code π N hN H) = H := by
  apply Subtype.ext
  change (H.1.map (QuotientGroup.mk' N)).comap (QuotientGroup.mk' N) = H.1
  rw [QuotientGroup.comap_map_mk']
  exact sup_eq_right.mpr (kernel_le π N H)

@[simp] theorem code_decode (L : SectionSubgroup (quotientProjection π N hN)) :
    code π N hN (decode π N hN L) = L := by
  apply Subtype.ext
  exact Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective N) L.1

end FixedKernelSubgroupFibre

variable (π : Q →* B) (N : Subgroup Q) [N.Normal] (hN : N ≤ π.ker)

/-- Exact quotient correspondence for the whole original fixed-kernel
fibre, without a count or lift-existence premise. -/
def fixedKernelSectionEquiv : FixedKernelSubgroupFibre π N ≃
    SectionSubgroup (QuotientGroup.lift N π hN) where
  toFun := FixedKernelSubgroupFibre.code π N hN
  invFun := FixedKernelSubgroupFibre.decode π N hN
  left_inv := FixedKernelSubgroupFibre.decode_code π N hN
  right_inv := FixedKernelSubgroupFibre.code_decode π N hN

def fixedKernelLiftEquiv : FixedKernelSubgroupFibre π N ≃
    HomomorphicLift (QuotientGroup.lift N π hN) (MonoidHom.id B) :=
  (fixedKernelSectionEquiv π N hN).trans
    (sectionSubgroupEquiv (QuotientGroup.lift N π hN))

/-- Literal reconstruction of the original subgroup from the unique
section of its original quotient. -/
@[simp] theorem fixedKernelLiftEquiv_symm_val
    (s : HomomorphicLift (QuotientGroup.lift N π hN) (MonoidHom.id B)) :
    ((fixedKernelLiftEquiv π N hN).symm s).1 =
      s.1.range.comap (QuotientGroup.mk' N) := rfl

/-- All exclusions on the original subgroup survive the correspondence. -/
def fixedKernelLiftRestrictedEquiv (P : Subgroup Q → Prop) :
    {H : FixedKernelSubgroupFibre π N // P H.1} ≃
      {s : HomomorphicLift (QuotientGroup.lift N π hN) (MonoidHom.id B) //
        P (s.1.range.comap (QuotientGroup.mk' N))} :=
  (fixedKernelLiftEquiv π N hN).subtypeEquiv (fun H => by
    change P H.1 ↔ P (((fixedKernelLiftEquiv π N hN).symm
      (fixedKernelLiftEquiv π N hN H)).1)
    rw [Equiv.symm_apply_apply])

def fixedKernelCocycleEquiv
    (s₀ : HomomorphicLift (QuotientGroup.lift N π hN) (MonoidHom.id B)) :
    FixedKernelSubgroupFibre π N ≃ KernelCocycle (QuotientGroup.lift N π hN) s₀.1 :=
  (fixedKernelLiftEquiv π N hN).trans
    (homomorphicLiftEquivCocycle (QuotientGroup.lift N π hN) (MonoidHom.id B) s₀)

theorem fixedKernelSubgroupFibre_card
    (s₀ : HomomorphicLift (QuotientGroup.lift N π hN) (MonoidHom.id B)) :
    Nat.card (FixedKernelSubgroupFibre π N) =
      Nat.card (KernelCocycle (QuotientGroup.lift N π hN) s₀.1) :=
  Nat.card_congr (fixedKernelCocycleEquiv π N hN s₀)

end SymmetricSubgroupAsymptotics

end
