import SymmetricSubgroupAsymptotics.TernaryFourSignedStabilizerCapacity
import SymmetricSubgroupAsymptotics.SignedMonomialSupportOrbitIndex
import SymmetricSubgroupAsymptotics.TernaryFourCoordinateSupportShells
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Tactic.Ring

/-! The actual signed fixed-stabilizer class weight on F3^4 is at most
330 times the SAME acting subgroup's order. Support indices and class
capacities are multiplied before cancellation, retaining their correlation. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical BigOperators
namespace SymmetricSubgroupAsymptotics.TernaryFourSignedFixedClassWeight
open TernarySignedWreathLinearEquiv TernaryFourProperModuleSignKernel
open SignedMonomialStabilizerClassBound TernaryFourSignedStabilizerCapacity
open TernaryFourCoordinateSupportShells

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

private theorem support_card_of_mem_shell (v : Fin 4 → ZMod 3) (k : ℕ)
    (hv : v∈shell k) : Nat.card {i : Fin 4 // v i≠0}=k := by
  have h : supportSize v=k := (Finset.mem_filter.mp hv).2
  simpa only [Nat.card_eq_fintype_card,Fintype.card_subtype,supportSize] using h

private theorem nonzero_of_mem_positive_shell (v : Fin 4 → ZMod 3) (k : ℕ)
    (hk : 0<k) (hv : v∈shell k) : v≠0 := by
  intro he
  have h : supportSize v=k := (Finset.mem_filter.mp hv).2
  rw [he] at h
  have hz : supportSize (0 : Fin 4 → ZMod 3)=0 := by simp [supportSize]
  omega

theorem sum_fixed_class_weight_le (R : Subgroup Signed)
    (ht : Function.Surjective (topHom R)) :
    (∑v : Fin 4 → ZMod 3,
      Nat.card (fixedSubgroup ((linearHom (Fin 4)).comp R.subtype) v)*
        Nat.card (ConjClasses (fixedSubgroup ((linearHom (Fin 4)).comp R.subtype) v)))≤
      330*Nat.card R := by
  let ρ := (linearHom (Fin 4)).comp R.subtype
  let s : (Fin 4 → ZMod 3) → ℕ := fun v => Nat.card (fixedSubgroup ρ v)
  let c : (Fin 4 → ZMod 3) → ℕ := fun v => Nat.card (ConjClasses (fixedSubgroup ρ v))
  have hindex (v : Fin 4 → ZMod 3) (k : ℕ) (hv : v∈shell k) :
      (4 : ℕ).choose k*s v≤Nat.card R := by
    have h := SignedMonomialSupportOrbitIndex.support_choose_mul_stabilizer_le
      ρ (topHom R) (fun g i => coefficient (Fin 4) g.val i)
      (fun g w i => linearHom_apply (Fin 4) g.val w i) ht v
    simpa only [Nat.card_fin,support_card_of_mem_shell v k hv] using h
  have hpositive (k den cap out : ℕ) (hk : 0<k) (hden : 0<den)
      (hchoose : (4 : ℕ).choose k=den) (hcap : supportBudget k=cap)
      (hcard : (shell k).card*cap=den*out) :
      (∑v∈shell k,s v*c v)≤out*Nat.card R := by
    apply sum_weight_le (shell k) s c (Nat.card R) den cap out hden hcard
    · intro v hv
      simpa only [hchoose] using hindex v k hv
    · intro v hv
      have h := nonzero_stabilizer_class_card_le R v (nonzero_of_mem_positive_shell v k hk hv)
      simpa only [support_card_of_mem_shell v k hv,hcap] using h
  have h0 : (∑v∈shell 0,s v*c v)≤42*Nat.card R := by
    apply sum_weight_le (shell 0) s c (Nat.card R) 1 42 42 (by decide)
      (by rw [shell_card ⟨0,by decide⟩]; decide)
    · intro v _
      exact (one_mul (s v)).le.trans
        (Nat.card_le_card_of_injective (fixedSubgroup ρ v).subtype Subtype.val_injective)
    · intro v hv
      have hzero : v=0 := by
        funext i
        by_contra hi
        letI : Nonempty {i : Fin 4 // v i≠0} := ⟨⟨i,hi⟩⟩
        have hp : 0<Nat.card {i : Fin 4 // v i≠0} := Nat.card_pos
        rw [support_card_of_mem_shell v 0 hv] at hp
        omega
      have he : fixedSubgroup ρ v=⊤ := by
        rw [hzero]
        ext g
        change ρ g 0=0 ↔ True
        exact iff_of_true (map_zero _) trivial
      change Nat.card (ConjClasses (fixedSubgroup ρ v))≤42
      rw [he,conjugacyClass_card_congr (Subgroup.topEquiv : (⊤ : Subgroup R) ≃* R)]
      exact subgroup_class_card_le_fortyTwo R ht
  have h1 := hpositive 1 4 48 96 (by decide) (by decide) (by decide) (by decide)
    (by rw [shell_card ⟨1,by decide⟩]; decide)
  have h2 := hpositive 2 6 16 64 (by decide) (by decide) (by decide) (by decide)
    (by rw [shell_card ⟨2,by decide⟩]; decide)
  have h3 := hpositive 3 4 6 48 (by decide) (by decide) (by decide) (by decide)
    (by rw [shell_card ⟨3,by decide⟩]; decide)
  have h4 := hpositive 4 1 5 80 (by decide) (by decide) (by decide) (by decide)
    (by rw [shell_card ⟨4,by decide⟩]; decide)
  have hsum := Finset.sum_fiberwise_of_maps_to
    (s:=Finset.univ) (t:=Finset.range 5) (g:=supportSize)
    (fun v _ => Finset.mem_range.mpr (by have h := supportSize_le_four v; omega))
    (fun v => s v*c v)
  change (∑k∈Finset.range 5,∑v∈shell k,s v*c v)=(∑v,s v*c v) at hsum
  change (∑v,s v*c v)≤330*Nat.card R
  rw [←hsum]
  simp only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add]
  omega

end SymmetricSubgroupAsymptotics.TernaryFourSignedFixedClassWeight
