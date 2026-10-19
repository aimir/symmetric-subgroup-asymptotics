import SymmetricSubgroupAsymptotics.OriginalKernelDualFixedTopCount
import SymmetricSubgroupAsymptotics.Non2PreE7B6RankTailSource

/-! A fixed top lift is determined by its kernel restriction and values
on lifts of generators of the top. The finite coefficient therefore uses
the number of top generators, rather than the order of the top. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.OriginalKernelDualFixedGeneratorCount

variable {Q T J : Type} [Group Q] [Group T] [Group J]

theorem eq_of_kernel_and_generators (theta : J →* T)
    (S : Finset T) (hS : Subgroup.closure (S : Set T) = ⊤)
    (s : S → J) (hs : ∀ t, theta (s t) = t.val)
    (phi chi : J →* Q)
    (hker : ∀ x : theta.ker, phi x = chi x)
    (hvalues : ∀ t, phi (s t) = chi (s t)) : phi = chi := by
  let L := phi.eqLocus chi
  have hk : theta.ker ≤ L := by
    intro x hx
    exact hker ⟨x,hx⟩
  have hmap : L.map theta = ⊤ := by
    apply top_unique
    rw [← hS]
    apply (Subgroup.closure_le (L.map theta)).mpr
    intro t ht
    exact Subgroup.mem_map.mpr ⟨s ⟨t,ht⟩,hvalues ⟨t,ht⟩,hs ⟨t,ht⟩⟩
  ext g
  have hg : theta g ∈ L.map theta := by rw [hmap]; trivial
  obtain ⟨x,hx,hxg⟩ := Subgroup.mem_map.mp hg
  have hkg : x⁻¹*g ∈ theta.ker := by
    change theta (x⁻¹*g)=1
    rw [map_mul,map_inv,hxg,inv_mul_cancel]
  have hmem := L.mul_mem hx (hk hkg)
  simpa only [mul_inv_cancel_left] using hmem

variable (pi : Q →* T) (A : Rep.{0} (ZMod 2) T)
    (E : OriginalKernelModuleChart pi A) (theta : J →* T)

include E in
theorem fixed_top_card_le_generators [Finite Q] [Finite J]
    (htheta : Function.Surjective theta)
    (S : Finset T) (hS : Subgroup.closure (S : Set T) = ⊤) {H : ℕ}
    (hgen : RepresentationGeneratedBy A.ρ.dual H) :
    Nat.card (OriginalKernelDualFixedTopCount.Lift pi theta) ≤
      Nat.card Q ^ S.card * 2 ^ (H * binaryCharacterRank theta.ker) := by
  have hdual : RepresentationGeneratedBy (Representation.dual (A.ρ.comp theta)) H := by
    rw [representation_dual_comp]
    exact representationGeneratedBy_comp_of_surjective A.ρ.dual theta htheta hgen
  letI := representationGenerated_intertwiner_finite (Representation.dual (A.ρ.comp theta))
    (DerivedHead.conjRep 2 J theta.ker) hdual
  letI : Finite (EquivariantBinaryRestrictionCount.Restriction theta.ker
      (A.ρ.comp theta)) := Finite.of_injective
    (EquivariantBinaryRestrictionCount.encode theta.ker (A.ρ.comp theta))
    (EquivariantBinaryRestrictionCount.encode_injective theta.ker (A.ρ.comp theta))
  let s : S → J := fun t => Classical.choose (htheta t.val)
  have hs (t : S) : theta (s t)=t.val := Classical.choose_spec (htheta t.val)
  let encoding : OriginalKernelDualFixedTopCount.Lift pi theta → (S → Q) ×
      EquivariantBinaryRestrictionCount.Restriction theta.ker (A.ρ.comp theta) :=
    fun phi => (fun t => phi.val (s t),OriginalKernelDualFixedTopCount.restriction pi A E theta phi)
  have hi : Function.Injective encoding := by
    intro phi chi h
    apply Subtype.ext
    apply eq_of_kernel_and_generators theta S hS s hs phi.val chi.val
    · intro x
      have hr := congrArg (fun z => z.2.hom (Additive.ofMul x)) h
      have hv := congrArg (fun v : A => (E.equiv (Multiplicative.ofAdd v) : Q)) hr
      simpa [encoding,OriginalKernelDualFixedTopCount.restriction] using hv
    · intro t
      exact congrArg (fun z => z.1 t) h
  have hc := EquivariantBinaryRestrictionCount.card_le theta.ker (A.ρ.comp theta) hdual
  have hh := Nat.card_le_card_of_injective encoding hi
  rw [Nat.card_prod,Nat.card_fun] at hh
  have hcard : Nat.card S = S.card := by
    rw [Nat.card_eq_fintype_card,Fintype.card_coe]
  rw [hcard] at hh
  exact hh.trans (Nat.mul_le_mul_left _ hc)

include E in
theorem fixed_top_card_le_log [Finite Q] [Finite T] [Finite J]
    (htheta : Function.Surjective theta) {H : ℕ}
    (hgen : RepresentationGeneratedBy A.ρ.dual H) :
    Nat.card (OriginalKernelDualFixedTopCount.Lift pi theta) ≤
      Nat.card Q ^ Nat.log 2 (Nat.card T) *
        2 ^ (H * binaryCharacterRank theta.ker) := by
  obtain ⟨S,hS,hpow⟩ := exists_generating_finset_two_pow_le T
  have hsize : S.card ≤ Nat.log 2 (Nat.card T) :=
    Nat.le_log_of_pow_le (by norm_num) hpow
  exact (fixed_top_card_le_generators pi A E theta htheta S hS hgen).trans
    (Nat.mul_le_mul_right _ (Nat.pow_le_pow_right Nat.card_pos hsize))

end SymmetricSubgroupAsymptotics.OriginalKernelDualFixedGeneratorCount
