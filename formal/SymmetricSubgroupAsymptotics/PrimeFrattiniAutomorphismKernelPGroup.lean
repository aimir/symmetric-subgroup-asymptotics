import SymmetricSubgroupAsymptotics.AutomorphismGeneratingLiftDivisibility
import SymmetricSubgroupAsymptotics.PrimeFrattiniAutomorphismAction

/-! The actual prime-Frattini automorphism kernel is a p-group. Its
action on every lift of one fixed quotient generating tuple is free;
the complete lift-set cardinality is a power of the original Frattini
cardinality. No automorphism-group order formula is assumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.PrimeFrattiniAutomorphismKernelPGroup
open AutomorphismGeneratingLiftDivisibility

variable (p : ℕ) [Fact p.Prime] {N : Type*} [Group N] [Finite N]

theorem all_lifts_generate (hN : IsPGroup p N) {ι : Type*}
    (g : ι → N) (hgen : Subgroup.closure (Set.range g) = ⊤)
    (x : Lift (primeAbelianizationGroupMap p N) g) :
    Subgroup.closure (Set.range x.val) = ⊤ := by
  apply prime_generates_of_evaluation_span p hN x.val
  have he : (fun i => primeAbelianizationMap p N (Additive.ofMul (x.val i))) =
      (fun i => primeAbelianizationMap p N (Additive.ofMul (g i))) := by
    funext i
    exact congrArg Multiplicative.toAdd (x.property i)
  rw [he]
  exact primeEvaluation_span_eq_top_of_generates p g hgen

theorem card_dvd_frattini_pow_primeRank
    (hN : IsPGroup p N) (A : Subgroup (MulAut N))
    (htrivial : ∀ (a : A) (n : N),
      primeAbelianizationGroupMap p N (a.val n) = primeAbelianizationGroupMap p N n) :
    Nat.card A ∣ (Nat.card (frattini N)) ^
      Module.finrank (ZMod p) (PrimeCharacters p N) := by
  obtain ⟨g,hgen⟩ := exists_primeFrattini_generating_tuple p hN
  have hd := card_dvd_kernel_pow (primeAbelianizationGroupMap p N) g
    (all_lifts_generate p hN g hgen) A htrivial
  simpa only [primeAbelianizationGroupMap_ker p N hN,Fintype.card_fin] using hd

theorem isPGroup_of_trivial_primeFrattini_action
    (hN : IsPGroup p N) (A : Subgroup (MulAut N))
    (htrivial : ∀ (a : A) (n : N),
      primeAbelianizationGroupMap p N (a.val n) = primeAbelianizationGroupMap p N n) :
    IsPGroup p A := by
  have hd := card_dvd_frattini_pow_primeRank p hN A htrivial
  obtain ⟨a,ha⟩ := IsPGroup.iff_card.mp (hN.to_subgroup (frattini N))
  rw [ha,← pow_mul] at hd
  obtain ⟨b,_,hb⟩ := (Nat.dvd_prime_pow (Fact.out : p.Prime)).mp hd
  exact IsPGroup.of_card hb

theorem groupAction_kernel_isPGroup (hN : IsPGroup p N) :
    IsPGroup p (PrimeFrattiniAutomorphismAction.groupAction p N).ker := by
  apply isPGroup_of_trivial_primeFrattini_action p hN
  intro a n
  have he := DFunLike.congr_fun a.property (primeAbelianizationGroupMap p N n)
  change PrimeFrattiniAutomorphismAction.groupAction p N a.val
    (primeAbelianizationGroupMap p N n) = primeAbelianizationGroupMap p N n at he
  rw [PrimeFrattiniAutomorphismAction.groupAction_apply] at he
  exact he

end SymmetricSubgroupAsymptotics.PrimeFrattiniAutomorphismKernelPGroup
