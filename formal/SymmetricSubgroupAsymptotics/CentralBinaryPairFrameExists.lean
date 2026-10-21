import SymmetricSubgroupAsymptotics.BinaryCoverage
import SymmetricSubgroupAsymptotics.CentralTwoPairFrame
import SymmetricSubgroupAsymptotics.BinaryPairFrameKernelTransport

/-! A transitive binary action admits a deliberately central pair frame
whose actual kernel contains the global pair flip. This property is not
asserted for an arbitrary point-stabilizer-cover frame. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics

theorem transitive_central_binary_pair_frame_exists
    {X : Type} [Finite X] (n : ℕ) (U : Subgroup (Equiv.Perm X))
    [MulAction.IsPretransitive U X] (hU : IsPGroup 2 U)
    (hdegree : Nat.card X = 2 ^ (n + 1)) :
    ∃ F : BinaryPairFrame U (Fin (2 ^ n)), ∃ z : F.top.ker,
      ∀ i, F.bits z i = 1 := by
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  letI : Nontrivial X := Finite.one_lt_card_iff_nontrivial.mp (by
    rw [hdegree, pow_succ]
    have hp : 0 < 2 ^ n := pow_pos (by decide) _
    omega)
  obtain ⟨x, y, hxy⟩ := exists_pair_ne X
  obtain ⟨u, hu⟩ := MulAction.exists_smul_eq U x y
  letI : Nontrivial U := ⟨⟨u, 1, by
    intro he
    apply hxy
    rw [he, one_smul] at hu
    exact hu⟩⟩
  obtain ⟨z, _, hzcenter, hzorder⟩ := pGroup_normal_contains_central_prime hU
    (⊤ : Subgroup U) (by exact top_ne_bot)
  let C : Subgroup U := Subgroup.zpowers z
  have hCcenter : C ≤ Subgroup.center U := Subgroup.zpowers_le.mpr hzcenter
  have hCcard : Nat.card C = 2 := (Nat.card_zpowers z).trans hzorder
  letI : C.Normal := ⟨fun a ha b => by
    simpa only [Subgroup.mem_center_iff.mp (hCcenter ha) b, mul_inv_cancel_right] using ha⟩
  have hz_ne : z ≠ 1 := by
    intro he
    rw [he, orderOf_one] at hzorder
    omega
  let F := CentralTwoPairFrame.frame U C x hCcenter hCcard
  let zC : C := ⟨z, Subgroup.mem_zpowers z⟩
  let zF : F.top.ker :=
    ⟨z, CentralTwoPairFrame.kernel_le U C x hCcenter hCcard zC.property⟩
  have hbits (i : CentralTwoPairFrame.Points U C x) : F.bits zF i = 1 := by
    exact CentralTwoPairFrame.bits_one U C x hCcenter hCcard zC
      (fun he => hz_ne (congrArg Subtype.val he)) i
  have hcard : Nat.card (CentralTwoPairFrame.Points U C x) = 2 ^ n := by
    have hd := CentralTwoPairFrame.degree_product U C x hCcenter hCcard
    rw [hdegree, pow_succ] at hd
    omega
  let e := Finite.equivFinOfCardEq hcard
  refine ⟨F.reindex e, F.reindexKernel e zF, ?_⟩
  intro i
  rw [F.reindexKernel_bits]
  exact hbits _

end SymmetricSubgroupAsymptotics
