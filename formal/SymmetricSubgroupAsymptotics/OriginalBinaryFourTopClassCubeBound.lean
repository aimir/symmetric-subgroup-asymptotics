import SymmetricSubgroupAsymptotics.CyclicOrbitCountMovedPointDeficit
import SymmetricSubgroupAsymptotics.BinaryBlockUnsignedKernelCoordinates
import SymmetricSubgroupAsymptotics.FourPointPermutationClassBound
import SymmetricSubgroupAsymptotics.OriginalMinimalBlockComponentTransport
import SymmetricSubgroupAsymptotics.GaronziMarotiLargeBlockReduction

/-! The identity reserve closes every original transitive four-block
binary extension. Correlated kernels and nonsplit extensions are retained;
no primitive-top or full-base condition is imposed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.OriginalBinaryFourTopClassCubeBound
open OriginalBlockClassBound BinaryBlockUnsignedKernelCoordinates

variable {A Ω X : Type} [Group A] [MulAction A Ω] [MulAction A X]
    [MulAction.IsPretransitive A X] [Finite A] [Finite Ω] [Finite X] [FaithfulSMul A Ω]

omit [MulAction.IsPretransitive A X] [Finite A] [Finite X] in
private theorem quotientHom_injective :
    Function.Injective (quotientHom (A:=A) (X:=X)) := by
  apply (injective_iff_map_eq_one _).mpr
  intro q hq
  induction q using QuotientGroup.induction_on with
  | H a => exact (QuotientGroup.eq_one_iff a).mpr hq

theorem class_card_le_fortyTwo
    (π : Ω → X) (hπ : ∀ (g : A) (ω : Ω),π (g • ω)=g • π ω)
    (hsize : ∀ x,Nat.card (originalBlockFibre π x)≤2)
    (hn : Nat.card X=4) : Nat.card (ConjClasses A)≤42 := by
  let N := Kernel (A:=A) (X:=X)
  letI : IsMulCommutative N :=
    BinaryBlockKernelAbelian.kernel_isMulCommutative π hπ hsize
  letI : MulAction (A ⧸ N) X := quotientAction (A:=A) (X:=X)
  letI : MulAction.IsPretransitive (A ⧸ N) X := ⟨fun x y => by
    obtain ⟨a,ha⟩ := MulAction.exists_smul_eq A x y
    exact ⟨QuotientGroup.mk a,ha⟩⟩
  letI : Nonempty X := Finite.card_pos_iff.mp (by omega : 0<Nat.card X)
  have hdiv : 4 ∣ Nat.card (A ⧸ N) := by
    have h := (MulAction.stabilizer (A ⧸ N) (Classical.choice (inferInstance : Nonempty X))).index_dvd_card
    simpa only [MulAction.index_stabilizer_of_transitive,hn] using h
  have hclasses : Nat.card (ConjClasses (A ⧸ N))≤5 := by
    let e := QuotientGroup.quotientKerEquivRange (topMap (A:=A) (X:=X))
    have htop := FourPointPermutationClassBound.faithful_action_class_card_le_five
      (Top (A:=A) (X:=X)) X hn
    exact (Nat.card_le_card_of_surjective (ConjClasses.map e.symm.toMonoidHom)
      (ConjClasses.map_surjective e.symm.surjective)).trans htop
  have hfixed : ∀q:A ⧸ N,q≠1 →
      Nat.card {u:N // AbelianExtensionConjugation.quotientConjugation N q u=u}≤8 := by
    intro q hq
    have hne : MulAction.toPermHom (A ⧸ N) X q≠1 := by
      intro he
      apply hq
      have hp : quotientHom (A:=A) (X:=X) q=1 := by
        apply Equiv.ext
        intro x
        have hx := congrArg (fun s : Equiv.Perm X => s x) he
        change quotientHom (A:=A) (X:=X) q x=x at hx
        exact hx
      exact quotientHom_injective (hp.trans (map_one (quotientHom (A:=A) (X:=X))).symm)
    have ho := CyclicOrbitCountMovedPointDeficit.cyclic_orbit_card_le_sub_one q hne
    have hf := AbelianExtensionUnsignedPermutationClassBound.fixed_card_le_cyclic_orbits
      N (coordinates π hπ) (coordinates_injective π hπ hsize)
      (quotient_intertwine π hπ hsize) q
    exact hf.trans ((Nat.pow_le_pow_right (by decide : 1≤2) ho).trans_eq (by rw [hn]))
  have hN : Nat.card N≤16 := by
    have h := BinaryBlockKernelAbelian.kernel_card_le_power π hπ hsize
    simpa only [hn,show 2^4=16 by decide] using h
  have hweighted := AbelianExtensionFixedSpaceClassBound.class_card_mul_quotient_le N 8 hfixed
  have hqpos : 0<Nat.card (A ⧸ N) := Nat.card_pos
  by_cases hfour : Nat.card (A ⧸ N)=4
  · have hc : Nat.card (ConjClasses (A ⧸ N))≤4 :=
      (Nat.card_le_card_of_surjective ConjClasses.mk ConjClasses.mk_surjective).trans_eq hfour
    rw [hfour] at hweighted
    nlinarith
  · have hq : 8≤Nat.card (A ⧸ N) := by
      obtain ⟨d,hd⟩ := hdiv
      omega
    nlinarith

theorem class_cube_le_of_four_binary_blocks
    (π : Ω → X) (hπ : ∀ (g : A) (ω : Ω),π (g • ω)=g • π ω)
    (hsize : ∀ x,Nat.card (originalBlockFibre π x)=2)
    (hn : Nat.card X=4) : Nat.card (ConjClasses A)^3≤5^(Nat.card Ω-1) := by
  have hc := class_card_le_fortyTwo π hπ (fun x => (hsize x).le) hn
  have hdegree : Nat.card Ω=8 := by
    have h := GaronziMarotiLargeBlockReduction.card_eq_blocks_mul_fibre π 2 hsize
    simpa only [hn] using h
  calc
    _≤42^3 := Nat.pow_le_pow_left hc 3
    _≤5^(Nat.card Ω-1) := by rw [hdegree]; decide

end SymmetricSubgroupAsymptotics.OriginalBinaryFourTopClassCubeBound

namespace SymmetricSubgroupAsymptotics.OriginalMinimalBlock
variable {A Ω : Type} [Group A] [MulAction A Ω] [MulAction.IsPretransitive A Ω]
    [Finite A] [Finite Ω] [FaithfulSMul A Ω]
    {ω₀ : Ω} (D : OriginalMinimalBlock (A:=A) ω₀)

theorem class_cube_le_of_four_binary_blocks
    (hc : Nat.card D.Fibre=2) (hn : Nat.card D.Points=4) :
    Nat.card (ConjClasses A)^3≤5^(Nat.card Ω-1) :=
  OriginalBinaryFourTopClassCubeBound.class_cube_le_of_four_binary_blocks
    D.map D.map_equivariant (fun x => (D.fibre_card_at x).trans hc) hn

end SymmetricSubgroupAsymptotics.OriginalMinimalBlock
