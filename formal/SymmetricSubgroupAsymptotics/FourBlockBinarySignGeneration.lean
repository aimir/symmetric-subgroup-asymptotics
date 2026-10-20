import SymmetricSubgroupAsymptotics.FourBlockBinarySignSpaces
import Mathlib.Algebra.Module.ZMod

/-! Symbolic generation of the actual signed four-block models. One
coordinate translation and the four-cycle generate every translation.
An adjacent sign pair generates the even signs by telescoping; a single
sign generates all signs. Only fixed four-coordinate identities are
checked finitely. No group or normal-subgroup census is used. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical BigOperators

namespace SymmetricSubgroupAsymptotics.FourBlockBinarySignGeneration

open SemidirectProduct BinarySignTernaryLinear FourBlockBinarySignSpaces
open TernaryFourBlockPermutationGenerators

section Translation

variable {p : ℕ} [Fact p.Prime] {R V : Type} [Group R]
  [AddCommGroup V] [Module (ZMod p) V] [FiniteDimensional (ZMod p) V]
  (rho : R →* (V ≃ₗ[ZMod p] V))
  (K : Subgroup (LinearSemidirectCoprimeSocleBounds.Model rho))

def translationSubmodule : Submodule (ZMod p) V :=
  AddSubgroup.toZModSubmodule p {
    carrier := {v | inl (Multiplicative.ofAdd v) ∈ K}
    zero_mem' := by simpa only [ofAdd_zero,map_one] using K.one_mem
    add_mem' := by
      intro v w hv hw
      change inl (Multiplicative.ofAdd (v+w)) ∈ K
      rw [ofAdd_add,map_mul]
      exact K.mul_mem hv hw
    neg_mem' := by
      intro v hv
      change inl (Multiplicative.ofAdd (-v)) ∈ K
      rw [ofAdd_neg,map_inv]
      exact K.inv_mem hv }

theorem translation_conjugate (g : LinearSemidirectCoprimeSocleBounds.Model rho)
    (hg : g ∈ K) (v : V) (hv : v ∈ translationSubmodule rho K) :
    rho g.right v ∈ translationSubmodule rho K := by
  have h := K.mul_mem (K.mul_mem hg hv) (K.inv_mem hg)
  rw [LinearSemidirectCoprimeSocleBounds.conjugate_translation] at h
  exact h

omit [FiniteDimensional (ZMod p) V] in
theorem eq_top_of_translations
    (hleft : translationSubmodule rho K = ⊤)
    (hright : ∀ r : R, inr r ∈ K) : K = ⊤ := by
  apply top_unique
  intro g _
  have h : g.left.toAdd ∈ translationSubmodule rho K := by
    rw [hleft]
    exact Submodule.mem_top
  rw [← inl_left_mul_inr_right g]
  exact K.mul_mem h (hright g.right)

end Translation

def shiftedSeed (even : Bool) (n : ℕ) : BinaryVector :=
  fun i => (if even then pair 0 1 else Pi.single 0 1) ((c^n)⁻¹ i)

theorem sign_span (even : Bool) (S : Submodule (ZMod 2) BinaryVector)
    (h : ∀ n : ℕ, shiftedSeed even n ∈ S)
    (v : BinaryVector) (hv : v ∈ (space (R := Equiv.Perm (Fin 4)) even).toSubmodule) :
    v ∈ S := by
  cases even
  · have hsingle (i : Fin 4) : (Pi.single i 1 : BinaryVector) ∈ S := by
      have hi := h i.val
      have he : shiftedSeed false i.val = Pi.single i 1 :=
        (by decide +kernel : ∀ j : Fin 4, shiftedSeed false j.val = Pi.single j 1) i
      rwa [he] at hi
    have he : (∑ i : Fin 4, v i • (Pi.single i 1 : BinaryVector)) = v := by
      calc
        _ = ∑ i, Pi.single i (v i) := by
          apply Finset.sum_congr rfl
          intro i _
          rw [← Pi.single_smul]
          simp
        _ = v := LinearMap.sum_single_apply (fun _ : Fin 4 => ZMod 2) v
    rw [← he]
    exact S.sum_mem fun i _ => S.smul_mem _ (hsingle i)
  · have hp (i : Fin 4) : pair 0 i ∈ S := by
      fin_cases i
      · change pair 0 0 ∈ S
        have he : pair 0 0 = 0 := by decide +kernel
        rw [he]
        exact S.zero_mem
      · exact h 0
      · change pair 0 2 ∈ S
        have he : pair 0 2 = shiftedSeed true 0 + shiftedSeed true 1 := by decide +kernel
        rw [he]
        exact S.add_mem (h 0) (h 1)
      · change pair 0 3 ∈ S
        have he : pair 0 3 = shiftedSeed true 0 + shiftedSeed true 1 + shiftedSeed true 2 := by
          decide +kernel
        rw [he]
        exact S.add_mem (S.add_mem (h 0) (h 1)) (h 2)
    have hsum : ∑ i : Fin 4, v i = 0 := hv
    have he : (∑ i : Fin 4, v i • pair 0 i) = v := by
      simp only [pair,smul_add,Finset.sum_add_distrib,← Finset.sum_smul,hsum,
        zero_smul,zero_add]
      calc
        _ = ∑ i, Pi.single i (v i) := by
          apply Finset.sum_congr rfl
          intro i _
          rw [← Pi.single_smul]
          simp
        _ = v := LinearMap.sum_single_apply (fun _ : Fin 4 => ZMod 2) v
    rw [← he]
    exact S.sum_mem fun i _ => S.smul_mem _ (hp i)

variable {R : Type} [Group R] [MulAction R (Fin 4)]
  (even : Bool) (r : R) (hr : ∀ i : Fin 4, r • i = c i)

include hr in
theorem power_action (n : ℕ) (i : Fin 4) : (r^n)⁻¹ • i = (c^n)⁻¹ i := by
  have he : MulAction.toPermHom R (Fin 4) r = c := Equiv.ext hr
  change MulAction.toPermHom R (Fin 4) ((r^n)⁻¹) i = _
  rw [map_inv,map_pow,he]

include hr in
theorem sign_model_eq_top
    (K : Subgroup (SignModel (space (R := R) even)))
    (hseed : inl (Multiplicative.ofAdd (signSeed (R := R) even)) ∈ K)
    (hc : inr r ∈ K) (hblocks : ∀ g : R, inr g ∈ K) : K = ⊤ := by
  let E := space (R := R) even
  let rho := CyclicOrbitBinarySignNormalGenerators.linearAction E
  let S := translationSubmodule rho K
  let U : Submodule (ZMod 2) BinaryVector := S.map E.toSubmodule.subtype
  have horbit (n : ℕ) : shiftedSeed even n ∈ U := by
    have hs : signSeed (R := R) even ∈ S := hseed
    have hpower : inr (r^n) ∈ K := by
      rw [map_pow]
      exact K.pow_mem hc n
    have hn := translation_conjugate rho K (inr (r^n)) hpower _ hs
    refine ⟨rho (r^n) (signSeed (R := R) even),hn,?_⟩
    funext i
    change (signSeed (R := R) even).1 ((r^n)⁻¹ • i) = shiftedSeed even n i
    rw [power_action r hr]
    cases even <;> rfl
  apply eq_top_of_translations rho K ?_ hblocks
  apply top_unique
  intro v _
  have hv : v.1 ∈ U := sign_span even U horbit v.1 v.2
  obtain ⟨w,hw,he⟩ := hv
  have hwe : w = v := Subtype.ext he
  rwa [hwe] at hw

abbrev AffineModel := BinarySignTernaryAffineSocles.Model (space (R := R) even)

include hr in
theorem affine_model_eq_top
    (K : Subgroup (AffineModel (R := R) even))
    (htranslation : inl (Multiplicative.ofAdd (Pi.single 0 1 : Vector)) ∈ K)
    (hsigns : inr (inl (Multiplicative.ofAdd (signSeed (R := R) even))) ∈ K)
    (hcycle : inr (inr r) ∈ K)
    (hblocks : ∀ g : R, inr (inr g) ∈ K) : K = ⊤ := by
  let E := space (R := R) even
  let rho := linearHom E
  have hsign : ∀ g : SignModel E, inr g ∈ K := by
    have ht : K.comap inr = ⊤ :=
      sign_model_eq_top even r hr (K.comap inr) hsigns hcycle hblocks
    intro g
    have hg : g ∈ K.comap inr := by rw [ht]; exact Subgroup.mem_top _
    exact hg
  apply eq_top_of_translations rho K ?_ hsign
  let S := translationSubmodule rho K
  have hsingle (i : Fin 4) : (Pi.single i 1 : Vector) ∈ S := by
    have hs : (Pi.single 0 1 : Vector) ∈ S := htranslation
    have hpower : inr (inr (r^i.val)) ∈ K := by
      rw [map_pow,map_pow]
      exact K.pow_mem hcycle i.val
    have hn := translation_conjugate rho K (inr (inr (r^i.val))) hpower _ hs
    have he : rho (inr (r^i.val)) (Pi.single 0 1) = Pi.single i 1 := by
      rw [BinarySignTernaryLinear.single_inr]
      have hi : r^i.val • (0 : Fin 4) = i := by
        have hp : MulAction.toPermHom R (Fin 4) r = c := Equiv.ext hr
        change MulAction.toPermHom R (Fin 4) (r^i.val) 0 = i
        rw [map_pow,hp]
        exact (by decide +kernel : ∀ j : Fin 4, (c^j.val) 0 = j) i
      rw [hi]
    exact he ▸ hn
  apply top_unique
  intro v _
  have he : (∑ i : Fin 4, v i • (Pi.single i 1 : Vector)) = v := by
    calc
      _ = ∑ i, Pi.single i (v i) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [← Pi.single_smul]
        simp
      _ = v := LinearMap.sum_single_apply (fun _ : Fin 4 => ZMod 3) v
  rw [← he]
  exact S.sum_mem fun i _ => S.smul_mem _ (hsingle i)

include hr in
theorem action_range_eq
    {ι : Type} (generators : ι → Equiv.Perm (Fin 12))
    (lifts : ι → AffineModel (R := R) even)
    (hbind : ∀ i, BinarySignTernaryPointAction.action (space (R := R) even) (lifts i) = generators i)
    (ht : BinarySignTernaryPointAction.action (space (R := R) even)
      (inl (Multiplicative.ofAdd (Pi.single 0 1 : Vector))) ∈
        Subgroup.closure (Set.range generators))
    (hs : BinarySignTernaryPointAction.action (space (R := R) even)
      (inr (inl (Multiplicative.ofAdd (signSeed (R := R) even)))) ∈
        Subgroup.closure (Set.range generators))
    (hc : BinarySignTernaryPointAction.action (space (R := R) even) (inr (inr r)) ∈
        Subgroup.closure (Set.range generators))
    (hblocks : ∀ K : Subgroup R, r ∈ K →
      (∀ i, (lifts i).right.right ∈ K) → K = ⊤)
    (hpure : ∀ i, BinarySignTernaryPointAction.action (space (R := R) even)
      (inr (inr (lifts i).right.right)) ∈ Subgroup.closure (Set.range generators)) :
    (BinarySignTernaryPointAction.action (space (R := R) even)).range =
      Subgroup.closure (Set.range generators) := by
  let f := BinarySignTernaryPointAction.action (space (R := R) even)
  let T := Subgroup.closure (Set.range generators)
  let K := T.comap f
  have hb : ∀ g : R, inr (inr g) ∈ K := by
    let B : Subgroup R := K.comap (inr.comp inr)
    have hB : B = ⊤ := hblocks B hc hpure
    intro g
    have hg : g ∈ B := by rw [hB]; exact Subgroup.mem_top _
    exact hg
  have hK : K = ⊤ := affine_model_eq_top even r hr K ht hs hc hb
  apply le_antisymm
  · rintro _ ⟨g,rfl⟩
    have hg : g ∈ K := by rw [hK]; exact Subgroup.mem_top _
    exact hg
  · apply (Subgroup.closure_le _).mpr
    rintro _ ⟨i,rfl⟩
    exact ⟨lifts i,hbind i⟩

end SymmetricSubgroupAsymptotics.FourBlockBinarySignGeneration

end
