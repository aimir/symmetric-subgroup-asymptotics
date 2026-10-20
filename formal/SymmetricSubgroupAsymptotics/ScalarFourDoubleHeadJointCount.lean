import SymmetricSubgroupAsymptotics.ScalarFourInvariantTwistedCount

/-! Actual index-three targets with two invariant binary coordinates and
two scalar-F4 coordinates. Missing central coordinates may be zero. The
joint coordinate map must be injective on the actual top kernel. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics

structure ScalarFourDoubleHeadJointData (Q : Type) [Group Q] where
  headed : ScalarFourHeadedQuotient Q
  first : Fin (headed.layers + 1)
  second : Fin (headed.layers + 1)
  invariant : Fin 2 → (headed.top.ker →* Multiplicative (ZMod 2))
  invariant_conj : ∀ q p j,
    invariant j (MulAut.conjNormal q p) = invariant j p
  joint : Function.Injective (fun p : headed.top.ker =>
    ((invariant 0 p, invariant 1 p),
      (headed.coord first p, headed.coord second p)))

namespace ScalarFourDoubleHeadJointData
variable {Q J : Type} [Group Q] [Finite Q] [Group J] [Finite J]
  (D : ScalarFourDoubleHeadJointData Q)

/-- Joint invariant/twisted restrictions over a fixed original source top. -/
theorem fibre_card_le (theta : J →* CyclicThree)
    (htheta : Function.Surjective theta) :
    Nat.card {phi : GroupEpimorphism J Q // D.headed.top.comp phi.1 = theta} ≤
      Nat.card Q * 2 ^ (2 * binaryCharacterRank theta.ker) := by
  obtain ⟨x, hx⟩ := htheta (Multiplicative.ofAdd 1)
  let F := theta.ker
  let R := {phi : GroupEpimorphism J Q // D.headed.top.comp phi.1 = theta}
  let restr : R → (F →* D.headed.top.ker) := fun phi =>
    (phi.1.1.comp F.subtype).codRestrict D.headed.top.ker (by
      intro f
      have he := DFunLike.congr_fun phi.2 (f : J)
      simp only [MonoidHom.comp_apply] at he
      rw [MonoidHom.mem_ker]
      simp only [MonoidHom.comp_apply, Subgroup.coe_subtype, he]
      exact f.2)
  have hdet : Function.Injective (fun phi : R => (phi.1.1 x, restr phi)) := by
    intro phi psi he
    obtain ⟨heval, hr⟩ := Prod.mk.inj he
    apply Subtype.ext
    apply Subtype.ext
    ext g
    let m := (Multiplicative.toAdd (theta g)).val
    have hmem : (x ^ m)⁻¹ * g ∈ F := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, map_pow, hx]
      have hm : (Multiplicative.ofAdd (1 : ZMod 3)) ^ m = theta g := by
        rw [← ofAdd_nsmul, nsmul_eq_mul, mul_one]
        simp [m]
      rw [hm, inv_mul_cancel]
    have hf := congrArg Subtype.val (DFunLike.congr_fun hr ⟨_, hmem⟩)
    change phi.1.1 ((x ^ m)⁻¹ * g) = psi.1.1 ((x ^ m)⁻¹ * g) at hf
    rw [map_mul, map_mul, map_inv, map_inv, map_pow, map_pow, heval] at hf
    exact mul_left_cancel hf
  let component : R → Fin 2 → ScalarFourInvariantTwistedPair F
      (fun f => MulAut.conjNormal x f) := fun phi j =>
    { invariant := (D.invariant j).comp (restr phi)
      twisted := (D.headed.coord (if j = 0 then D.first else D.second)).comp (restr phi)
      invariant_fixed := by
        intro f
        have he : restr phi (MulAut.conjNormal x f) =
            MulAut.conjNormal (phi.1.1 x) (restr phi f) := by
          apply Subtype.ext
          simp [restr]
        change D.invariant j (restr phi (MulAut.conjNormal x f)) = _
        rw [he, D.invariant_conj]
        rfl
      twisted_action := by
        intro f
        have he : restr phi (MulAut.conjNormal x f) =
            MulAut.conjNormal (phi.1.1 x) (restr phi f) := by
          apply Subtype.ext
          simp [restr]
        change D.headed.coord _ (restr phi (MulAut.conjNormal x f)) = _
        rw [he, D.headed.coord_twisted]
        have htop : D.headed.top (phi.1.1 x) = Multiplicative.ofAdd 1 := by
          have hh := DFunLike.congr_fun phi.2 x
          simp only [MonoidHom.comp_apply] at hh
          rw [hh, hx]
        rw [htop]
        rfl }
  let encode : R → Q ×
      (ScalarFourInvariantTwistedPair F (fun f => MulAut.conjNormal x f) ×
       ScalarFourInvariantTwistedPair F (fun f => MulAut.conjNormal x f)) :=
    fun phi => (phi.1.1 x, component phi 0, component phi 1)
  have hinj : Function.Injective encode := by
    intro phi psi he
    have hx : phi.1.1 x = psi.1.1 x :=
      congrArg (fun z : Q ×
        (ScalarFourInvariantTwistedPair F (fun f => MulAut.conjNormal x f) ×
         ScalarFourInvariantTwistedPair F (fun f => MulAut.conjNormal x f)) => z.1) he
    apply hdet
    apply Prod.ext
    · exact hx
    · apply MonoidHom.ext
      intro f
      change restr phi f = restr psi f
      apply D.joint
      have h0 := congrArg (fun z => z.2.1) he
      have h1 := congrArg (fun z => z.2.2) he
      have hi0 := DFunLike.congr_fun
        (congrArg ScalarFourInvariantTwistedPair.invariant h0) f
      have hi1 := DFunLike.congr_fun
        (congrArg ScalarFourInvariantTwistedPair.invariant h1) f
      have ht0 := DFunLike.congr_fun
        (congrArg ScalarFourInvariantTwistedPair.twisted h0) f
      have ht1 := DFunLike.congr_fun
        (congrArg ScalarFourInvariantTwistedPair.twisted h1) f
      exact Prod.ext (Prod.ext hi0 hi1)
        (Prod.ext (by simpa [component] using ht0) (by simpa [component] using ht1))
  letI : Finite (F →* Multiplicative (ZMod 2)) :=
    Finite.of_injective
      (fun f : F →* Multiplicative (ZMod 2) => (f : F → Multiplicative (ZMod 2)))
      DFunLike.coe_injective
  letI : Finite (ScalarFourInvariantTwistedPair F
      (fun f => MulAut.conjNormal x f)) :=
    Finite.of_injective ScalarFourInvariantTwistedPair.encode
      ScalarFourInvariantTwistedPair.encode_injective
  calc Nat.card R ≤ Nat.card (Q ×
        (ScalarFourInvariantTwistedPair F (fun f => MulAut.conjNormal x f) ×
         ScalarFourInvariantTwistedPair F (fun f => MulAut.conjNormal x f))) :=
      Nat.card_le_card_of_injective encode hinj
    _ = Nat.card Q * Nat.card
        (ScalarFourInvariantTwistedPair F (fun f => MulAut.conjNormal x f) ×
         ScalarFourInvariantTwistedPair F (fun f => MulAut.conjNormal x f)) :=
      Nat.card_prod _ _
    _ ≤ Nat.card Q * 2 ^ (2 * binaryCharacterRank F) :=
      Nat.mul_le_mul_left _ ScalarFourInvariantTwistedPair.pair_card_le

end ScalarFourDoubleHeadJointData
end SymmetricSubgroupAsymptotics
end
