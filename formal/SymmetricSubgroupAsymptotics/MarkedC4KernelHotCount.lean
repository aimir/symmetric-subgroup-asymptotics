import SymmetricSubgroupAsymptotics.FiniteTopKernelRankHot
import SymmetricSubgroupAsymptotics.MarkedC4KernelRankTailNumerics
import SymmetricSubgroupAsymptotics.Non2PreE7B6RankTailSource

/-! Full C4-character tails on an actual finite-index kernel. The encoding
retains the literal kernel and all coset representatives. No C4 character
count is replaced by binary rank. -/
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators
namespace SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu
namespace MarkedC4KernelHotCount

abbrev C4 := Multiplicative (ZMod 4)

def Hot (a : ℝ) {b : ℕ} (F : Subgroup (Equiv.Perm (Fin b))) : Prop :=
  (2 : ℝ)^(a*b) < Nat.card (F →* C4)

def KernelHot (T : Type) [Group T] (a : ℝ) {b : ℕ}
    (J : Subgroup (Equiv.Perm (Fin b))) : Prop :=
  ∃ theta : J →* T, Function.Surjective theta ∧
    (2 : ℝ)^(a*b) < Nat.card (theta.ker →* C4)

/-- A literal full-mark tail, valid at every moment order, including zero. -/
theorem hot_card_le (a : ℝ) (b r : ℕ) :
    ((Finset.univ.filter (fun F : Subgroup (Equiv.Perm (Fin b)) => Hot a F)).card : ℝ) ≤
      (2 : ℝ)^(-((r : ℝ)*a*b))*markedC4Moment b r := by
  let t : ℝ := (2 : ℝ)^(a*b)
  have ht : 0 < t := by dsimp [t]; positivity
  have hpow : t^r*((Finset.univ.filter
      (fun F : Subgroup (Equiv.Perm (Fin b)) => Hot a F)).card : ℝ) ≤
      markedC4Moment b r := by
    calc
      _ = ∑ _F ∈ Finset.univ.filter
          (fun F : Subgroup (Equiv.Perm (Fin b)) => Hot a F), t^r := by
        rw [Finset.sum_const,nsmul_eq_mul,mul_comm]
      _ ≤ ∑ F ∈ Finset.univ.filter
          (fun F : Subgroup (Equiv.Perm (Fin b)) => Hot a F),
          (Nat.card (F →* C4) : ℝ)^r := by
        apply Finset.sum_le_sum
        intro F hF
        exact pow_le_pow_left₀ ht.le ((Finset.mem_filter.mp hF).2.le) r
      _ ≤ ∑ F : Subgroup (Equiv.Perm (Fin b)), (Nat.card (F →* C4) : ℝ)^r :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun _ _ _ => by positivity)
      _ = _ := rfl
  have he : t^r = (2 : ℝ)^((r : ℝ)*a*b) := by
    dsimp [t]
    rw [← Real.rpow_natCast,← Real.rpow_mul (by norm_num : (0 : ℝ)≤2)]
    congr 1
    ring
  rw [he] at hpow
  rw [Real.rpow_neg (by norm_num : (0 : ℝ)≤2),← div_eq_inv_mul,
    le_div_iff₀ (by positivity : (0 : ℝ)<(2 : ℝ)^((r : ℝ)*a*b)),mul_comm]
  exact hpow

variable (T : Type) [Group T] [Finite T]

/-- The same actual hot kernel and a section recover the original source. -/
theorem kernel_hot_card_le (a : ℝ) (b : ℕ) :
    Nat.card {J : Subgroup (Equiv.Perm (Fin b)) // KernelHot T a J} ≤
      Nat.factorial b ^ Nat.card T *
        Nat.card {F : Subgroup (Equiv.Perm (Fin b)) // Hot a F} := by
  let HJ := {J : Subgroup (Equiv.Perm (Fin b)) // KernelHot T a J}
  let HF := {F : Subgroup (Equiv.Perm (Fin b)) // Hot a F}
  have hw : ∀ J : HJ, ∃ theta : J.val →* T, ∃ s : T → J.val,
      (∀ t, theta (s t)=t) ∧ (2 : ℝ)^(a*b) < Nat.card (theta.ker →* C4) := by
    intro J
    obtain ⟨theta,htheta,hhot⟩ := J.property
    choose s hs using htheta
    exact ⟨theta,s,hs,hhot⟩
  choose theta s hs hhot using hw
  let enc : HJ → HF × (T → Equiv.Perm (Fin b)) := fun J =>
    (⟨(theta J).ker.map J.val.subtype,by
      unfold Hot
      have hc := Nat.card_congr
        ((Subgroup.equivMapOfInjective (theta J).ker J.val.subtype
          Subtype.val_injective).monoidHomCongrLeftEquiv (N:=C4))
      rw [← hc]
      exact hhot J⟩,fun t => (s J t : Equiv.Perm (Fin b)))
  have hi : Function.Injective enc := by
    intro J K h
    have hk := congrArg (fun z : HF × (T → Equiv.Perm (Fin b)) => z.1.val) h
    have he := congrArg (fun z : HF × (T → Equiv.Perm (Fin b)) => z.2) h
    dsimp only [enc] at hk he
    apply Subtype.ext
    rw [eq_closure_kernel_section T J.val (theta J) (s J) (hs J),
      eq_closure_kernel_section T K.val (theta K) (s K) (hs K),hk,he]
  have h := Nat.card_le_card_of_injective enc hi
  rw [Nat.card_prod,Nat.card_fun,Nat.card_perm,Nat.card_fin] at h
  exact h.trans_eq (Nat.mul_comm _ _)

theorem kernel_hot_card_real_le (a : ℝ) (b r : ℕ) :
    ((Finset.univ.filter (fun J : Subgroup (Equiv.Perm (Fin b)) =>
      KernelHot T a J)).card : ℝ) ≤
      (Nat.factorial b : ℝ)^Nat.card T *
        ((2 : ℝ)^(-((r : ℝ)*a*b))*markedC4Moment b r) := by
  have hJc : (Finset.univ.filter (fun J : Subgroup (Equiv.Perm (Fin b)) =>
      KernelHot T a J)).card =
      Nat.card {J : Subgroup (Equiv.Perm (Fin b)) // KernelHot T a J} := by
    rw [Nat.card_eq_fintype_card,Fintype.card_subtype]
  have hFc : (Finset.univ.filter (fun F : Subgroup (Equiv.Perm (Fin b)) =>
      Hot a F)).card = Nat.card {F : Subgroup (Equiv.Perm (Fin b)) // Hot a F} := by
    rw [Nat.card_eq_fintype_card,Fintype.card_subtype]
  have hc : ((Finset.univ.filter (fun J : Subgroup (Equiv.Perm (Fin b)) =>
      KernelHot T a J)).card : ℝ) ≤ (Nat.factorial b : ℝ)^Nat.card T *
      ((Finset.univ.filter (fun F : Subgroup (Equiv.Perm (Fin b)) =>
      Hot a F)).card : ℝ) := by
    rw [hJc,hFc]
    exact_mod_cast kernel_hot_card_le T a b
  exact hc.trans (mul_le_mul_of_nonneg_left (hot_card_le a b r) (by positivity))

/-- The whole target fibre survives on a hot source, with only its fixed
factorial loss. -/
theorem kernel_hot_epi_sum_le (Q : Type) [Group Q] [Finite Q]
    (m : ℕ) (hQ : Nat.card Q ≤ 2^m) (b : ℕ) :
    (∑ J ∈ Finset.univ.filter (fun J : Subgroup (Equiv.Perm (Fin b)) =>
      KernelHot T (51/200) J), (Nat.card (GroupEpimorphism J Q) : ℝ)) ≤
      MarkedC4KernelRankTailNumerics.raw 1 (m+Nat.card T) b := by
  calc
    _ ≤ ∑ _J ∈ Finset.univ.filter (fun J : Subgroup (Equiv.Perm (Fin b)) =>
        KernelHot T (51/200) J), (Nat.factorial b : ℝ)^m := by
      apply Finset.sum_le_sum
      intro J _
      exact_mod_cast groupEpimorphism_card_le_factorial_pow J hQ
    _ = ((Finset.univ.filter (fun J : Subgroup (Equiv.Perm (Fin b)) =>
        KernelHot T (51/200) J)).card : ℝ)*(Nat.factorial b : ℝ)^m := by
      rw [Finset.sum_const,nsmul_eq_mul]
    _ ≤ ((Nat.factorial b : ℝ)^Nat.card T *
        ((2 : ℝ)^(-((MarkedC4KernelRankTailNumerics.tilt b : ℝ)*(51/200)*b))*
          markedC4Moment b (MarkedC4KernelRankTailNumerics.tilt b)))*
        (Nat.factorial b : ℝ)^m :=
      mul_le_mul_of_nonneg_right
        (kernel_hot_card_real_le T (51/200) b (MarkedC4KernelRankTailNumerics.tilt b))
        (by positivity)
    _ = _ := by unfold MarkedC4KernelRankTailNumerics.raw; rw [pow_add]; ring

end MarkedC4KernelHotCount
end SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu
