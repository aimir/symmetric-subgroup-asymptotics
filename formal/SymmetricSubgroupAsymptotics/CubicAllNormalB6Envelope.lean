import SymmetricSubgroupAsymptotics.CubicKernelCoordinateEnvelope
import SymmetricSubgroupAsymptotics.CubicOriginalNormalQuotientChart
import SymmetricSubgroupAsymptotics.CubicOutsideKernelBinaryQuotient

/-! One structural B6 envelope for every actual normal quotient. Original
kernel coordinates control both invariant and scalar components at once.
Normal subgroups inside the kernel use the canonical original module
quotient. Those meeting the top use the small actual binary image. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics
namespace CubicAllNormalB6Envelope

variable {G : Type} [Group G] [Finite G]
  (top : G →* CyclicThree) (htop : Function.Surjective top)
  (A : Rep (ZMod 2) CyclicThree) (E : OriginalKernelModuleChart top A)
  (D : CubicBinaryCoordinates A.ρ)
  (hscalar : ∃ j : Fin 2, ∃ p : top.ker,
    CubicElementaryKernelCoordinates.scalar top A.ρ E.equiv.symm D j p ≠ 1)

include A E D in
private theorem kernel_card_le : Nat.card top.ker ≤ 64 := by
  let c : top.ker →
      ((Multiplicative (ZMod 2) × Multiplicative (ZMod 2)) × (ScalarFour × ScalarFour)) :=
    fun p => ((CubicElementaryKernelCoordinates.invariant top A.ρ E.equiv.symm D 0 p,
      CubicElementaryKernelCoordinates.invariant top A.ρ E.equiv.symm D 1 p),
      (CubicElementaryKernelCoordinates.scalar top A.ρ E.equiv.symm D 0 p,
      CubicElementaryKernelCoordinates.scalar top A.ρ E.equiv.symm D 1 p))
  have hc := Nat.card_le_card_of_injective c
    (CubicElementaryKernelCoordinates.joint top A.ρ E.equiv.symm D)
  have htarget : Nat.card
      ((Multiplicative (ZMod 2) × Multiplicative (ZMod 2)) × (ScalarFour × ScalarFour)) = 64 := by
    norm_num [ScalarFour,Nat.card_eq_fintype_card]
  exact hc.trans_eq htarget

include hscalar in
private theorem kernel_selfCentralizing (g : G)
    (hcomm : ∀ k : top.ker, g * k = k * g) : g ∈ top.ker := by
  obtain ⟨j,p,hp⟩ := hscalar
  have he : MulAut.conjNormal g p = p := by
    apply Subtype.ext
    change g*(p : G)*g⁻¹=(p : G)
    rw [hcomm p]
    group
  have htw := CubicElementaryKernelCoordinates.scalar_conj top A.ρ E.equiv.symm D
    (CubicKernelCoordinateEnvelope.inverseChart_conjugate top A E) g p j
  rw [he] at htw
  have hz := scalarFourTwist_fixed hp htw.symm
  exact MonoidHom.mem_ker.mpr (Multiplicative.toAdd.injective hz)

/-- Every actual normal quotient is paid without a finite normal census. -/
def quotientCertificate (hKP : KovacsPraegerAbelianizationBound)
    (N : Subgroup G) [N.Normal] :
    PreE7B6QuotientCertificate (G ⧸ N) := by
  by_cases hN : N ≤ top.ker
  · let qtop := QuotientGroup.lift N top hN
    have hqtop : Function.Surjective qtop := by
      intro c
      obtain ⟨g,hg⟩ := htop c
      exact ⟨QuotientGroup.mk' N g,hg⟩
    let B := CubicOriginalNormalQuotientChart.quotientModule top htop A E N
    let F := CubicOriginalNormalQuotientChart.quotientChart top htop A E N hN
    let C := CubicOriginalNormalQuotientChart.quotientCoordinates top htop A E N D
    exact CubicKernelCoordinateEnvelope.certificate qtop hqtop B F C hKP
  · have hp : IsPGroup 2 top.ker :=
      (ZModModule.isPGroup_multiplicative (n := 2) (G := A)).of_injective
        E.equiv.symm.toMonoidHom E.equiv.symm.injective
    exact CubicOutsideKernelBinaryQuotient.certificate top hp
      (kernel_card_le top A E D) (kernel_selfCentralizing top A E D hscalar) N hN

end CubicAllNormalB6Envelope
end SymmetricSubgroupAsymptotics
end
