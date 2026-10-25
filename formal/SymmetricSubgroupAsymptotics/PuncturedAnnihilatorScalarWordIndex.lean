import SymmetricSubgroupAsymptotics.CentralExtensionScalarWordIndex
import SymmetricSubgroupAsymptotics.SubgroupInvariantPuncturedSetOrbitIndex

/-! A nonzero dual orbit stays in the punctured annihilator. The
resulting scalar-word capacity concerns the SAME central intersection,
vector image and join as the original normal-layer index identity.
No larger-field linearity of the subgroup is asserted. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.PuncturedAnnihilatorScalarWordIndex
open InvariantAnnihilatorOrbitIndex CentralExtensionScalarPairingIndex
open CentralExtensionScalarPairingCentre ScalarCentrePrimeFieldAction

theorem dual_orbit_card_le_punctured_quotient_card_mul_index
    {F G U : Type*} [Field F] [Group G] [AddCommGroup U] [Module F U]
    [Finite F] [Finite G] [Finite U] [Module.Finite F U]
    (ρ : G →* U ≃ₗ[F] U) (L : Subgroup G) (J : Submodule F U)
    (hJ : ∀ g ∈ L, ∀ u ∈ J, ρ g u ∈ J)
    (φ : J.dualAnnihilator) (hφ : φ.val ≠ 0) :
    Nat.card (dualOrbit ρ φ.val) ≤ (Nat.card (U ⧸ J)-1)*L.index := by
  letI : MulAction G (Module.Dual F U) := dualAction ρ
  letI : Finite (Module.Dual F U) := Finite.of_injective
    (fun ψ : Module.Dual F U => (ψ : U → F)) DFunLike.coe_injective
  letI : Finite (U ⧸ J) := Finite.of_surjective J.mkQ J.mkQ_surjective
  have hzero (g : G) : g • (0 : Module.Dual F U)=0 := by
    apply LinearMap.ext
    intro u
    rfl
  have hA : ∀ g : L, ∀ ψ ∈ (J.dualAnnihilator : Set (Module.Dual F U)),
      g • ψ ∈ (J.dualAnnihilator : Set (Module.Dual F U)) := by
    intro g ψ hψ
    change ψ.comp (ρ g.val⁻¹).toLinearMap ∈ J.dualAnnihilator
    change ψ ∈ J.dualAnnihilator at hψ
    rw [Submodule.mem_dualAnnihilator] at hψ ⊢
    intro u hu
    exact hψ _ (hJ g.val⁻¹ (L.inv_mem g.property) u hu)
  have hh := SubgroupInvariantPuncturedSetOrbitIndex.orbit_card_le_invariant_set_sub_one_mul_index
    L (J.dualAnnihilator : Set (Module.Dual F U)) (0 : Module.Dual F U) φ.val
    J.dualAnnihilator.zero_mem φ.property hφ hzero hA
  have hc : Nat.card J.dualAnnihilator=Nat.card (U ⧸ J) :=
    (Nat.card_congr (Subspace.quotEquivAnnihilator J).toEquiv).symm
  have hh' : Nat.card (dualOrbit ρ φ.val) ≤ (Nat.card J.dualAnnihilator-1)*L.index := hh
  rw [hc] at hh'
  exact hh'

theorem index_power_succ_le_of_scalar_words
    {P K V : Type*} [Group P] [Finite P] [Field K] [Finite K]
    [AddCommGroup V] [Module K V] [Finite V]
    (N : Subgroup P) [N.Normal]
    (D : Data (F := K) (V := V) (N := N))
    (p m : ℕ) [Fact p.Prime] [CharP K p]
    (hdim : Module.finrank K V=2*m)
    (χ : P →* MulAut (Multiplicative K))
    (hequiv : ∀ g a, D.central (χ g a)=MulAut.conjNormal g (D.central a))
    (hscalar : ∀ a : Kˣ, ∃ g : P, ∀ b : K,
      χ g (Multiplicative.ofAdd b)=Multiplicative.ofAdd ((a : K)*b))
    (M : Subgroup P) (hM : (D.central (Multiplicative.ofAdd (1 : K))).val ∉ M) :
    Nat.card K^(m+1) ≤ M.index := by
  letI : Algebra (ZMod p) K := ZMod.algebra K p
  letI : Module.Finite (ZMod p) K := Module.Finite.of_finite
  let J : Subgroup N := M.comap N.subtype
  let C : Subgroup (Multiplicative K) := J.comap D.central
  let W : Subgroup (Multiplicative V) := J.map D.projection
  let L : Subgroup P := M ⊔ N
  let A : Submodule (ZMod p) K := AddSubgroup.toZModSubmodule p C.toAddSubgroup'
  letI : Finite (K ⧸ A) := Finite.of_surjective A.mkQ A.mkQ_surjective
  let ρ : P →* K ≃ₗ[ZMod p] K := (linearAction p).comp χ
  have hJ : ¬D.central.range ≤ J := by
    intro hh
    exact hM (hh ⟨Multiplicative.ofAdd (1 : K),rfl⟩)
  have hw : Nat.card W ≤ Nat.card K^m := D.vectorImage_card_le p m hdim J hJ
  have hC : ∀ g ∈ L, ∀ a ∈ C, χ g a ∈ C :=
    ActualNormalLayerOrbitIndex.central_layer_invariant N M D.central D.central_injective
      (fun a => central_range_le_center D ⟨a,rfl⟩) χ hequiv
  have hA : ∀ g ∈ L, ∀ x ∈ A, ρ g x ∈ A := by
    intro g hg x hx
    exact hC g hg (Multiplicative.ofAdd x) hx
  have hAscalar : ∀ a : Kˣ, ∃ g : P, ∀ x : K, ρ g x=(a : K)*x := by
    intro a
    obtain ⟨g,hg⟩ := hscalar a
    exact ⟨g,fun x => congrArg Multiplicative.toAdd (hg x)⟩
  have h1 : (1 : K) ∉ A := hM
  obtain ⟨f,hf⟩ := exists_annihilator_nonzero_on A (1 : K) h1
  have hf0 : f.val ≠ 0 := by
    intro hh
    exact hf (by rw [hh]; rfl)
  have ho : Nat.card K-1 ≤ (Nat.card (K ⧸ A)-1)*L.index :=
    (ScalarWordDualAnnihilatorOrbitIndex.dual_orbit_card_ge ρ hAscalar f.val hf0).trans
      (dual_orbit_card_le_punctured_quotient_card_mul_index ρ L A hA f hf0)
  have hAC : Nat.card A=Nat.card C := Nat.card_congr
    ({ toFun := fun x => ⟨Multiplicative.ofAdd x.val,x.property⟩
       invFun := fun x => ⟨x.val.toAdd,x.property⟩
       left_inv := fun _ => rfl
       right_inv := fun _ => rfl } : A ≃ C)
  have hcard : Nat.card K=Nat.card (K ⧸ A)*Nat.card C := by
    calc
      Nat.card K=Nat.card A*Nat.card (K ⧸ A) := Submodule.card_eq_card_quotient_mul_card A
      _ = Nat.card (K ⧸ A)*Nat.card C := by rw [hAC]; exact Nat.mul_comm _ _
  have hsub : (Nat.card (K ⧸ A)-1)*Nat.card C ≤ Nat.card K-1 := by
    have hQpos : 0 < Nat.card (K ⧸ A) := Nat.card_pos
    have hCpos : 0 < Nat.card C := Nat.card_pos
    have he : (Nat.card (K ⧸ A)-1)*Nat.card C+Nat.card C=Nat.card K := by
      calc
        _ = (Nat.card (K ⧸ A)-1+1)*Nat.card C := by ring
        _ = Nat.card (K ⧸ A)*Nat.card C :=
          congrArg (fun n : ℕ => n*Nat.card C) (by omega)
        _ = Nat.card K := hcard.symm
    omega
  have hc : (Nat.card K-1)*Nat.card C ≤ (Nat.card K-1)*L.index := by
    calc
      _ ≤ ((Nat.card (K ⧸ A)-1)*L.index)*Nat.card C := Nat.mul_le_mul_right _ ho
      _ = ((Nat.card (K ⧸ A)-1)*Nat.card C)*L.index := by ring
      _ ≤ (Nat.card K-1)*L.index := Nat.mul_le_mul_right _ hsub
  have hCL : Nat.card C ≤ L.index := Nat.le_of_mul_le_mul_left hc
    (by have hq : 1 < Nat.card K := Finite.one_lt_card; omega)
  have he := ActualNormalLayerOrbitIndex.index_mul_layer_cards N M D.projection
    D.projection_surjective D.central D.central_range
  change M.index*Nat.card C*Nat.card W=Nat.card K*Nat.card (Multiplicative V)*L.index at he
  have hV : Nat.card (Multiplicative V)=Nat.card K^(2*m) := by
    change Nat.card V = _
    rw [Module.natCard_eq_pow_finrank (K := K),hdim]
  rw [hV] at he
  have hpre : (Nat.card K*Nat.card K^(2*m))*Nat.card C ≤
      (M.index*Nat.card K^m)*Nat.card C := by
    calc
      _ ≤ (Nat.card K*Nat.card K^(2*m))*L.index := Nat.mul_le_mul_left _ hCL
      _ = M.index*Nat.card C*Nat.card W := he.symm
      _ ≤ M.index*Nat.card C*Nat.card K^m := Nat.mul_le_mul_left _ hw
      _ = (M.index*Nat.card K^m)*Nat.card C := by ring
  have hp : Nat.card K^(m+1)*Nat.card K^m=Nat.card K*Nat.card K^(2*m) := by
    calc
      _ = (Nat.card K^m*Nat.card K)*Nat.card K^m :=
        congrArg (fun n : ℕ => n*Nat.card K^m) (pow_succ (Nat.card K) m)
      _ = Nat.card K*(Nat.card K^m*Nat.card K^m) := by ring
      _ = Nat.card K*Nat.card K^(m+m) := by rw [pow_add]
      _ = Nat.card K*Nat.card K^(2*m) :=
        congrArg (fun n : ℕ => Nat.card K*Nat.card K^n) (two_mul m).symm
  apply Nat.le_of_mul_le_mul_right ?_ (pow_pos (Nat.card_pos (α := K)) m)
  rw [hp]
  exact Nat.le_of_mul_le_mul_right hpre (Nat.card_pos (α := C))

end SymmetricSubgroupAsymptotics.PuncturedAnnihilatorScalarWordIndex
