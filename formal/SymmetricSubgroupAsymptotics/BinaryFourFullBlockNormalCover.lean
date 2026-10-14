import SymmetricSubgroupAsymptotics.BinaryFourFullBlockQuotient
import SymmetricSubgroupAsymptotics.BinaryFourFullBlockSubmodules

/-! Every normal subgroup of the full block source outside translations
contains the actual augmentation kernel. A nonzero normal block image
contains the displayed Klein involution; its commutators with eight
coordinate translations force six augmentation directions. -/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace BinaryFourFullBlockCoordinates

open BinaryFourBlockAugmentation SemidirectProduct

def ambientTranslationKernel : Subgroup Ambient :=
  (SemidirectProduct.rightHom : Ambient →* Complement).ker

instance : ambientTranslationKernel.Normal :=
  inferInstanceAs (SemidirectProduct.rightHom : Ambient →* Complement).ker.Normal

def ambientNormalSpace (N : Subgroup Ambient) : Submodule Scalar FullCoordinates where
  carrier := {x | (inl (Multiplicative.ofAdd x) : Ambient) ∈ N}
  zero_mem' := by simpa only [ofAdd_zero, map_one] using N.one_mem
  add_mem' := by
    intro x y hx hy
    change (inl (Multiplicative.ofAdd x * Multiplicative.ofAdd y) : Ambient) ∈ N
    rw [map_mul]
    exact N.mul_mem hx hy
  smul_mem' := by
    intro a x hx
    have ha : a = 0 ∨ a = 1 := by
      fin_cases a
      · exact Or.inl rfl
      · exact Or.inr rfl
    rcases ha with rfl | rfl
    · simpa only [zero_smul, ofAdd_zero, map_one] using N.one_mem
    · simpa only [one_smul] using hx

theorem ambientNormalSpace_conjugate (N : Subgroup Ambient) (hN : N.Normal)
    (g : Ambient) (x : FullCoordinates) (hx : x ∈ ambientNormalSpace N) :
    fullComplementLinear g.right x ∈ ambientNormalSpace N := by
  have h := hN.conj_mem _ hx g
  rw [ambient_conjugate_inl] at h
  exact h

theorem ambientNormalSpace_u (N : Subgroup Ambient) (hN : N.Normal)
    (x : FullCoordinates) (hx : x ∈ ambientNormalSpace N) :
    fullU x ∈ ambientNormalSpace N := by
  have h := ambientNormalSpace_conjugate N hN (inr uElement) x hx
  change fullComplementLinear uElement x ∈ ambientNormalSpace N at h
  rwa [fullLinear_u] at h

theorem ambientNormalSpace_v (N : Subgroup Ambient) (hN : N.Normal)
    (x : FullCoordinates) (hx : x ∈ ambientNormalSpace N) :
    fullV x ∈ ambientNormalSpace N := by
  have h := ambientNormalSpace_conjugate N hN (inr vElement) x hx
  change fullComplementLinear vElement x ∈ ambientNormalSpace N at h
  rwa [fullLinear_v] at h

theorem ambientNormalSpace_c (N : Subgroup Ambient) (hN : N.Normal)
    (x : FullCoordinates) (hx : x ∈ ambientNormalSpace N) :
    fullC x ∈ ambientNormalSpace N := by
  have h := ambientNormalSpace_conjugate N hN (inr cElement) x hx
  change fullComplementLinear cElement x ∈ ambientNormalSpace N at h
  rwa [fullLinear_c] at h

theorem ambientNormalSpace_difference (N : Subgroup Ambient) (hN : N.Normal)
    (g : Ambient) (hg : g ∈ N) (x : FullCoordinates) :
    fullComplementLinear g.right x - x ∈ ambientNormalSpace N := by
  let t : Ambient := inl (Multiplicative.ofAdd x)
  have h : g * t * g⁻¹ * t⁻¹ ∈ N := by
    have hc := hN.conj_mem g⁻¹ (N.inv_mem hg) t
    simpa only [mul_assoc] using N.mul_mem hg hc
  dsimp only [t] at h
  rw [ambient_conjugate_inl, ← map_inv, ← map_mul] at h
  change (inl (Multiplicative.ofAdd (fullComplementLinear g.right x - x)) : Ambient) ∈ N
  simpa only [ofAdd_sub, div_eq_mul_inv] using h

theorem outside_translation_lift_u (N : Subgroup Ambient) (hN : N.Normal)
    (hNE : ¬ N ≤ ambientTranslationKernel) : ∃ g ∈ N, g.right = uElement := by
  let pi : Ambient →* Complement := SemidirectProduct.rightHom
  have hmapN : (N.map pi).Normal := hN.map pi rightHom_surjective
  have hmapb : N.map pi ≠ ⊥ := by
    intro hb
    apply hNE
    intro g hg
    have h : pi g ∈ N.map pi := ⟨g, hg, rfl⟩
    rw [hb] at h
    exact Subgroup.mem_bot.mp h
  have hu : uElement ∈ N.map pi :=
    BinaryKleinTernaryNormalChain.kleinKernel_le_normal (N.map pi) hmapN hmapb (by rfl)
  obtain ⟨g, hg, hgu⟩ := hu
  exact ⟨g, hg, hgu⟩

theorem ambientNormalSpace_six_basis (N : Subgroup Ambient) (hN : N.Normal)
    (g : Ambient) (hgN : g ∈ N) (hg : g.right = uElement) :
    ∀ i : Fin 8, i.val < 6 → fullBasis i ∈ ambientNormalSpace N := by
  let W := ambientNormalSpace N
  have hd (i : Fin 8) : fullU (fullBasis i) - fullBasis i ∈ W := by
    have h := ambientNormalSpace_difference N hN g hgN (fullBasis i)
    rwa [hg, fullLinear_u] at h
  have h1 : fullBasis 1 ∈ W := by
    have he : fullU (fullBasis 2) - fullBasis 2 = fullBasis 1 := by
      ext i; revert i; decide +kernel
    rw [← he]
    exact hd 2
  have h0 : fullBasis 0 ∈ W := by
    have he : (fullU (fullBasis 4) - fullBasis 4) - fullBasis 1 = fullBasis 0 := by
      ext i; revert i; decide +kernel
    rw [← he]
    exact W.sub_mem (hd 4) h1
  have h3 : fullBasis 3 ∈ W := by
    have he : fullU (fullBasis 6) - fullBasis 6 = fullBasis 3 := by
      ext i; revert i; decide +kernel
    rw [← he]
    exact hd 6
  have h4 : fullBasis 4 ∈ W := by
    have he : fullC (fullBasis 3) = fullBasis 4 := by
      ext i; revert i; decide +kernel
    rw [← he]
    exact ambientNormalSpace_c N hN _ h3
  have h2 : fullBasis 2 ∈ W := by
    have he : fullC (fullBasis 4) = fullBasis 2 := by
      ext i; revert i; decide +kernel
    rw [← he]
    exact ambientNormalSpace_c N hN _ h4
  have h5 : fullBasis 5 ∈ W := by
    have he : ((fullU (fullBasis 7) - fullBasis 7) - fullBasis 3) - fullBasis 4 =
        fullBasis 5 := by
      ext i; revert i; decide +kernel
    rw [← he]
    exact W.sub_mem (W.sub_mem (hd 7) h3) h4
  intro i hi
  fin_cases i
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4
  · exact h5
  · change 6 < 6 at hi
    omega
  · change 7 < 6 at hi
    omega

theorem augmentation_vector_mem_of_six_basis
    (W : Submodule Scalar FullCoordinates)
    (hb : ∀ i : Fin 8, i.val < 6 → fullBasis i ∈ W)
    (x : FullCoordinates) (hx : augmentation x = 0) : x ∈ W := by
  have h6 : x 6 = 0 := congrFun hx 0
  have h7 : x 7 = 0 := congrFun hx 1
  have he : x = x 0 • fullBasis 0 + x 1 • fullBasis 1 + x 2 • fullBasis 2 +
      x 3 • fullBasis 3 + x 4 • fullBasis 4 + x 5 • fullBasis 5 := by
    ext i
    fin_cases i <;> simp [fullBasis, h6, h7]
  rw [he]
  exact W.add_mem (W.add_mem (W.add_mem (W.add_mem (W.add_mem
    (W.smul_mem _ (hb 0 (by decide))) (W.smul_mem _ (hb 1 (by decide))))
      (W.smul_mem _ (hb 2 (by decide)))) (W.smul_mem _ (hb 3 (by decide))))
        (W.smul_mem _ (hb 4 (by decide)))) (W.smul_mem _ (hb 5 (by decide)))

theorem fullBlockQuotient_kernel_cover (N : Subgroup Ambient) (hN : N.Normal)
    (hNE : ¬ N ≤ ambientTranslationKernel) : fullBlockQuotientMap.ker ≤ N := by
  obtain ⟨g, hgN, hg⟩ := outside_translation_lift_u N hN hNE
  intro e he
  obtain ⟨hr, ha⟩ := (fullBlockQuotientMap_kernel e).mp he
  have h := augmentation_vector_mem_of_six_basis (ambientNormalSpace N)
    (ambientNormalSpace_six_basis N hN g hgN hg) e.left.toAdd ha
  have heq : (inl (Multiplicative.ofAdd e.left.toAdd) : Ambient) = e :=
    SemidirectProduct.ext rfl hr.symm
  change (inl (Multiplicative.ofAdd e.left.toAdd) : Ambient) ∈ N at h
  rwa [heq] at h

end BinaryFourFullBlockCoordinates
end SymmetricSubgroupAsymptotics

end
