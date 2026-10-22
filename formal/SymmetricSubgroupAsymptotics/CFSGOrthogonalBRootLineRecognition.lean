import SymmetricSubgroupAsymptotics.CFSGOrthogonalBHighestRootLine
import SymmetricSubgroupAsymptotics.CFSGOrthogonalBUnipotentCenter
import SymmetricSubgroupAsymptotics.CFSGOrthogonalBBorelPowerElements
import SymmetricSubgroupAsymptotics.CFSGOrthogonalBUnipotentNormalizer

/-! A nonzero highest-root element intrinsically recovers its SAME
root line as the defining-prime-power elements in its double centralizer.
No full natural centralizer calculation or polar-label premise is used. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalBUnipotent
open CFSGOrthogonalBSerreMatrices
variable {K : Type} [Field K] [Finite K]

def PrimePowerDoubleCentralizer {G : Type*} [Group G] (p : ℕ) (x y : G) : Prop :=
  (∃ k : ℕ, y ^ (p ^ k) = 1) ∧ ∀ z : G, Commute z x → Commute y z

theorem mem_highestRootLine_iff_doubleCentralizer (p : ℕ) [Fact p.Prime] [CharP K p]
    (h2 : (2 : K) ≠ 0) (s : ℕ) (a : K) (ha : a ≠ 0)
    (y : elementaryRootGroup K (s + 3)) :
    y ∈ highestRootLine h2 s ↔ PrimePowerDoubleCentralizer p (highestRoot s a) y := by
  constructor
  · intro hy
    obtain ⟨b, rfl⟩ := (mem_highestRootLine_iff h2 s y).mp hy
    obtain ⟨k, hk⟩ := (unipotent_isPGroup K (s + 3) p)
      (⟨highestRoot s b, highestRoot_mem_unipotent h2 s b⟩ : unipotent K (s + 3))
    refine ⟨⟨k, congrArg Subtype.val hk⟩, ?_⟩
    intro z hz
    exact (commute_all_highestRoots_of_commute_nonzero h2 s z a ha hz b).symm
  · rintro ⟨⟨k, hk⟩, htest⟩
    have hroot := highestRoot_central p h2 s a
    have hux (u : elementaryRootGroup K (s + 3)) (hu : u ∈ unipotent K (s + 3)) :
        Commute u (highestRoot s a) := by
      have he := Subgroup.mem_center_iff.mp hroot ⟨u, hu⟩
      exact congrArg Subtype.val he
    have hyC : y ∈ Subgroup.centralizer
        (unipotent K (s + 3) : Set (elementaryRootGroup K (s + 3))) := by
      apply Subgroup.mem_centralizer_iff.mpr
      intro u hu
      exact (htest u (hux u hu)).symm
    have hyB : y ∈ borel K (s + 3) :=
      normalizer_unipotent_le_borel K h2 (s + 2)
        (Subgroup.centralizer_le_normalizer _ hyC)
    have hyU := pPower_element_mem_unipotent p (s + 3) y hyB k hk
    have hyZ : (⟨y, hyU⟩ : unipotent K (s + 3)) ∈
        Subgroup.center (unipotent K (s + 3)) := by
      apply Subgroup.mem_center_iff.mpr
      intro u
      apply Subtype.ext
      exact (htest u.val (hux u.val u.property)).symm
    obtain ⟨b, hb⟩ := central_unipotent_is_highestRoot h2 s ⟨y, hyU⟩ hyZ
    exact (mem_highestRootLine_iff h2 s y).mpr ⟨b, hb⟩

theorem doubleCentralizer_map_iff {G : Type*} [Group G] (p : ℕ)
    (f : MulAut G) (x y : G) :
    PrimePowerDoubleCentralizer p (f x) (f y) ↔ PrimePowerDoubleCentralizer p x y := by
  have hf (e : MulAut G) (a b : G) (h : PrimePowerDoubleCentralizer p a b) :
      PrimePowerDoubleCentralizer p (e a) (e b) := by
    obtain ⟨⟨k, hk⟩, ht⟩ := h
    refine ⟨⟨k, ?_⟩, ?_⟩
    · rw [← map_pow, hk, map_one]
    · intro z hz
      have hz' : Commute (e.symm z) a := by
        simpa only [e.symm_apply_apply] using hz.map e.symm
      simpa only [e.apply_symm_apply] using (ht (e.symm z) hz').map e
  constructor
  · intro h
    simpa only [f.symm_apply_apply] using hf f.symm (f x) (f y) h
  · exact hf f x y

end SymmetricSubgroupAsymptotics.CFSGOrthogonalBUnipotent
