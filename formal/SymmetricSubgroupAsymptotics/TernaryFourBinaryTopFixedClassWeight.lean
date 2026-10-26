import SymmetricSubgroupAsymptotics.TernaryFourBinaryTopStabilizerBounds
import SymmetricSubgroupAsymptotics.TernaryFourTransitiveSignedClassBound
import SymmetricSubgroupAsymptotics.TernaryFourCoordinateSupportShells
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Tactic.Ring

/-! Full translation class weights for the SAME transitive signed top
of order at most eight. Small sign kernel gives total356; a larger sign
kernel doubles the pair-support index and gives282. Both are at most360.
The only selected finite data are the previously checked 81 vector shells. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical BigOperators
namespace SymmetricSubgroupAsymptotics.TernaryFourBinaryTopFixedClassWeight
open TernarySignedWreathLinearEquiv TernaryFourProperModuleSignKernel
open SignedMonomialStabilizerClassBound TernaryFourCoordinateSupportShells
open TernaryFourBinaryTopStabilizerBounds

private theorem sum_weight_le {V : Type} (S : Finset V) (s c : V → ℕ)
    (q den cap out : ℕ) (hden : 0<den) (hcard : S.card*cap=den*out)
    (hs : ∀v∈S,den*s v≤q) (hc : ∀v∈S,c v≤cap) :
    (∑v∈S,s v*c v)≤out*q := by
  have h : den*(∑v∈S,s v*c v)≤den*(out*q) := by
    calc
      _=∑v∈S,den*(s v*c v) := by rw [Finset.mul_sum]
      _≤∑_v∈S,q*cap := by
        apply Finset.sum_le_sum
        intro v hv
        calc
          den*(s v*c v)=(den*s v)*c v := by ring
          _≤(den*s v)*cap := Nat.mul_le_mul_left _ (hc v hv)
          _≤q*cap := Nat.mul_le_mul_right _ (hs v hv)
      _=S.card*(q*cap) := by simp only [Finset.sum_const,nsmul_eq_mul,Nat.cast_id]
      _=(S.card*cap)*q := by ring
      _=den*(out*q) := by rw [hcard]; ring
  exact Nat.le_of_mul_le_mul_left h hden

private theorem support_card (v : Fin 4 → ZMod 3) (k : ℕ) (hv : v∈shell k) :
    Nat.card {i : Fin 4 // v i≠0}=k := by
  have h : supportSize v=k := (Finset.mem_filter.mp hv).2
  simpa only [Nat.card_eq_fintype_card,Fintype.card_subtype,supportSize] using h

private theorem zero_card (v : Fin 4 → ZMod 3) (k : ℕ) (hv : v∈shell k) :
    Nat.card {i : Fin 4 // v i=0}=4-k := by
  have hsum : Nat.card {i : Fin 4 // v i=0}+Nat.card {i : Fin 4 // v i≠0}=4 := by
    rw [←Nat.card_sum]
    exact (Nat.card_congr (Equiv.sumCompl (fun i : Fin 4 => v i=0))).trans (Nat.card_fin 4)
  rw [support_card v k hv] at hsum
  omega

private theorem nonzero_of_shell (v : Fin 4 → ZMod 3) (k : ℕ)
    (hk : 0<k) (hv : v∈shell k) : v≠0 := by
  intro he
  have h : supportSize v=k := (Finset.mem_filter.mp hv).2
  rw [he] at h
  have hz : supportSize (0 : Fin 4 → ZMod 3)=0 := by simp [supportSize]
  omega

private theorem nonempty_of_card_pos (P : Fin 4 → Prop)
    (h : 0<Nat.card {i : Fin 4 // P i}) : {i : Fin 4 | P i}.Nonempty := by
  obtain ⟨i⟩ := Finite.card_pos_iff.mp h
  exact ⟨i.val,i.property⟩

theorem sum_fixed_class_weight_le (R : Subgroup Signed)
    (htrans : ∀ i j : Fin 4,∃g : R,topHom R g i=j)
    (hQ : Nat.card (topHom R).range≤8) :
    (∑v : Fin 4 → ZMod 3,
      Nat.card (fixedSubgroup ((linearHom (Fin 4)).comp R.subtype) v)*
        Nat.card (ConjClasses (fixedSubgroup ((linearHom (Fin 4)).comp R.subtype) v)))≤
      360*Nat.card R := by
  let ρ := (linearHom (Fin 4)).comp R.subtype
  let s : (Fin 4 → ZMod 3) → ℕ := fun v => Nat.card (fixedSubgroup ρ v)
  let c : (Fin 4 → ZMod 3) → ℕ := fun v => Nat.card (ConjClasses (fixedSubgroup ρ v))
  have h1 : (∑v∈shell 1,s v*c v)≤32*Nat.card R := by
    apply sum_weight_le (shell 1) s c (Nat.card R) 4 16 32 (by decide)
      (by rw [shell_card ⟨1,by decide⟩]; decide)
    · intro v hv
      exact (unique_support_bounds R htrans hQ v (Or.inl (support_card v 1 hv))).1
    · intro v hv
      have h := (unique_support_bounds R htrans hQ v (Or.inl (support_card v 1 hv))).2
      rw [zero_card v 1 hv] at h
      exact h
  have h3 : (∑v∈shell 3,s v*c v)≤32*Nat.card R := by
    apply sum_weight_le (shell 3) s c (Nat.card R) 4 4 32 (by decide)
      (by rw [shell_card ⟨3,by decide⟩]; decide)
    · intro v hv
      exact (unique_support_bounds R htrans hQ v (Or.inr (zero_card v 3 hv))).1
    · intro v hv
      have h := (unique_support_bounds R htrans hQ v (Or.inr (zero_card v 3 hv))).2
      rw [zero_card v 3 hv] at h
      exact h
  have h4 : (∑v∈shell 4,s v*c v)≤80*Nat.card R := by
    apply sum_weight_le (shell 4) s c (Nat.card R) 1 5 80 (by decide)
      (by rw [shell_card ⟨4,by decide⟩]; decide)
    · intro v _
      exact (one_mul (s v)).le.trans
        (Nat.card_le_card_of_injective (fixedSubgroup ρ v).subtype Subtype.val_injective)
    · intro v hv
      have h := TernaryFourSignedStabilizerCapacity.nonzero_stabilizer_class_card_le R v
        (nonzero_of_shell v 4 (by decide) hv)
      rw [support_card v 4 hv] at h
      exact h
  have h0 (cap : ℕ) (hcap : Nat.card (ConjClasses R)≤cap) :
      (∑v∈shell 0,s v*c v)≤cap*Nat.card R := by
    apply sum_weight_le (shell 0) s c (Nat.card R) 1 cap cap (by decide)
      (by rw [shell_card ⟨0,by decide⟩]; simp)
    · intro v _
      exact (one_mul (s v)).le.trans
        (Nat.card_le_card_of_injective (fixedSubgroup ρ v).subtype Subtype.val_injective)
    · intro v hv
      have hzero : v=0 := by
        funext i
        by_contra hi
        letI : Nonempty {i : Fin 4 // v i≠0} := ⟨⟨i,hi⟩⟩
        have hp : 0<Nat.card {i : Fin 4 // v i≠0} := Nat.card_pos
        rw [support_card v 0 hv] at hp
        omega
      have he : fixedSubgroup ρ v=⊤ := by
        rw [hzero]
        ext g
        change ρ g 0=0 ↔ True
        exact iff_of_true (map_zero _) trivial
      change Nat.card (ConjClasses (fixedSubgroup ρ v))≤cap
      rw [he,conjugacyClass_card_congr (Subgroup.topEquiv : (⊤ : Subgroup R) ≃* R)]
      exact hcap
  have h2 (den out : ℕ) (hden : 0<den) (hcard : (shell 2).card*16=den*out)
      (hindex : ∀v∈shell 2,den*s v≤Nat.card R) :
      (∑v∈shell 2,s v*c v)≤out*Nat.card R := by
    apply sum_weight_le (shell 2) s c (Nat.card R) den 16 out hden hcard hindex
    intro v hv
    have h := TernaryFourSignedStabilizerCapacity.nonzero_stabilizer_class_card_le R v
      (nonzero_of_shell v 2 (by decide) hv)
    rw [support_card v 2 hv] at h
    exact h
  have hdata (v : Fin 4 → ZMod 3) (hv : v∈shell 2) :
      {i : Fin 4 | v i≠0}.Nonempty ∧ {i : Fin 4 | v i=0}.Nonempty := by
    constructor
    · exact nonempty_of_card_pos _ (by rw [support_card v 2 hv]; decide)
    · exact nonempty_of_card_pos _ (by rw [zero_card v 2 hv]; decide)
  have hsum := Finset.sum_fiberwise_of_maps_to
    (s:=Finset.univ) (t:=Finset.range 5) (g:=supportSize)
    (fun v _ => Finset.mem_range.mpr (by have h := supportSize_le_four v; omega))
    (fun v => s v*c v)
  change (∑k∈Finset.range 5,∑v∈shell k,s v*c v)=(∑v,s v*c v) at hsum
  change (∑v,s v*c v)≤360*Nat.card R
  rw [←hsum]
  simp only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add]
  by_cases hsmall : Nat.card (topHom R).ker≤4
  · have hzeroR : Nat.card (ConjClasses R)≤20 :=
      (TernaryFourTransitiveSignedClassBound.class_card_le_sign_kernel_mul_five R).trans
        (by nlinarith)
    have hzero := h0 20 hzeroR
    have hpair := h2 2 192 (by decide) (by rw [shell_card ⟨2,by decide⟩]; decide)
      (fun v hv => proper_support_index R htrans v (hdata v hv).1 (hdata v hv).2)
    omega
  · have hlarge : 4<Nat.card (topHom R).ker := by omega
    have hzero := h0 42 (TernaryFourTransitiveSignedClassBound.class_card_le_fortyTwo R htrans)
    have hpair := h2 4 96 (by decide) (by rw [shell_card ⟨2,by decide⟩]; decide)
      (fun v hv => large_kernel_pair_support_index R htrans v
        (hdata v hv).1 (hdata v hv).2 (zero_card v 2 hv) hlarge)
    omega

end SymmetricSubgroupAsymptotics.TernaryFourBinaryTopFixedClassWeight
