import SymmetricSubgroupAsymptotics.ActualLocalChiefSteps
import SymmetricSubgroupAsymptotics.DegreeSixOwnerCoinducedHead

/-!
# Local chief layers over an abelian block kernel

When the source of a local chief evaluation lies in an abelian normal block
kernel, that kernel acts trivially on the literal induced image.  The image
therefore descends to the faithful top, using the canonical evaluation-image
fibre from `SurjectiveCoinducedDescent`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics

variable {A V : Type} [Group A] [Finite A]
    [AddCommGroup V] [Module (ZMod 3) V]

/-- An abelian ambient kernel centralizes every local source lying inside it,
so it kills the actual local induced quotient representation. -/
theorem localChiefInducedImage_kernel_of_le_commutative
    (K N H : Subgroup A) [N.Normal] [IsMulCommutative K]
    (hNK : N ≤ K)
    (ρ : Representation (ZMod 3) H V)
    (φ : N →* Multiplicative V)
    (he : ∀ (h : H) (n : N),
      (φ (MulAut.conjNormal (h : A) n)).toAdd = ρ h (φ n).toAdd) :
    K ≤ (localChiefInducedImage H (normalChainSourceAction N) ρ φ he).toRepresentation.ker := by
  intro k hk
  apply MonoidHom.mem_ker.mpr
  apply LinearMap.ext
  intro v
  obtain ⟨n, hn⟩ := localChiefQuotientMap_surjective H
    (normalChainSourceAction N) ρ φ he (Multiplicative.ofAdd v)
  have hcomm : (k : A) * (n : A) = (n : A) * (k : A) := by
    let kk : K := ⟨k, hk⟩
    let nn : K := ⟨n, hNK n.2⟩
    exact congrArg Subtype.val (IsMulCommutative.is_comm.comm kk nn)
  have hconj : normalChainSourceAction N (k : A) n = n := by
    apply Subtype.ext
    change (k : A) * (n : A) * (k : A)⁻¹ = (n : A)
    rw [hcomm, mul_assoc, mul_inv_cancel, mul_one]
  have hq := localChiefQuotientMap_equivariant H
    (normalChainSourceAction N) ρ φ he (k : A) n
  rw [hconj, hn] at hq
  apply Multiplicative.toAdd.injective
  exact congrArg Multiplicative.toAdd hq.symm


/-- Once the top is in either sharp degree-six owner, an elementary local
chief layer lying in an abelian quotient kernel contributes at most its
literal fibre dimension. -/
theorem localChiefInducedImage_characterHead_le_fibre_of_owners
    {Q : Type} [Group Q] [Finite Q]
    [FiniteDimensional (ZMod 3) V]
    (π : A →* Q) (hπ : Function.Surjective π)
    (N H : Subgroup A) [N.Normal]
    (hNH : N ≤ π.ker) (hKH : π.ker ≤ H)
    [IsMulCommutative π.ker]
    (ρ : Representation (ZMod 3) H V)
    (φ : N →* Multiplicative V)
    (he : ∀ (h : H) (n : N),
      (φ (MulAut.conjNormal (h : A) n)).toAdd = ρ h (φ n).toAdd)
    (hOwner :
      (∃ g : Q, MulAction.IsPretransitive (Subgroup.zpowers g)
        (Q ⧸ subgroupImage π H)) ∨
      (∃ W : C1CyclicBinaryModuleOwnerWitness Q,
        Nat.card W.complement = 3)) :
    Module.finrank (ZMod 3)
      (primeActionCharacters 3
        (representationGroupAction
          (localChiefInducedImage H (normalChainSourceAction N) ρ φ he).toRepresentation)) ≤
      Module.finrank (ZMod 3) V := by
  let M : Subrepresentation (Representation.ind H.subtype ρ) :=
    localChiefInducedImage H (normalChainSourceAction N) ρ φ he
  let τ : Representation (ZMod 3) A M.toSubmodule := M.toRepresentation
  let ψ : τ.IntertwiningMap (Representation.coind H.subtype ρ) :=
    (inducedElementCoinducedEquiv H ρ).toIntertwiningMap.comp
      (ThreeGroupHead.inclusion (Representation.ind H.subtype ρ) M)
  have hψ : Function.Injective ψ :=
    (inducedElementCoinducedEquiv H ρ).toLinearEquiv.injective.comp
      Subtype.val_injective
  have hτ : π.ker ≤ τ.ker :=
    localChiefInducedImage_kernel_of_le_commutative π.ker N H hNH ρ φ he
  let R : Subrepresentation ρ := intertwinerEvaluationImage H ρ τ ψ
  let ρQ := fibreRepresentationDescend π H R.toRepresentation
    (evaluationImage_fibreKernel π H hKH ρ τ hτ ψ)
  let τQ := representationDescend π hπ τ hτ
  let ψQ : τQ.IntertwiningMap
      (Representation.coind (subgroupImage π H).subtype ρQ) :=
    coinducedIntertwinerDescendViaEvaluationImage π hπ H hKH ρ τ hτ ψ
  have hψQ : Function.Injective ψQ :=
    coinducedIntertwinerDescendViaEvaluationImage_injective
      π hπ H hKH ρ τ hτ ψ hψ
  have hTop : Module.finrank (ZMod 3)
      (primeActionCharacters 3 (representationGroupAction τQ)) ≤
      Module.finrank (ZMod 3) R.toSubmodule := by
    rcases hOwner with ⟨g, hg⟩ | ⟨W, hW⟩
    · letI : MulAction.IsPretransitive (Subgroup.zpowers g)
          (Q ⧸ subgroupImage π H) := hg
      exact coinduced_injective_characterHead_le_fibre_of_pretransitive
        (subgroupImage π H) ρQ g τQ ψQ hψQ
    · exact W.coinduced_injective_characterHead_le_fibre
        hW (subgroupImage π H) ρQ τQ ψQ hψQ
  calc
    Module.finrank (ZMod 3)
        (primeActionCharacters 3 (representationGroupAction
          (localChiefInducedImage H (normalChainSourceAction N) ρ φ he).toRepresentation)) =
        Module.finrank (ZMod 3)
          (τ.IntertwiningMap (Representation.trivial (ZMod 3) A (ZMod 3))) :=
      (representationCharacterHeadEquiv τ).finrank_eq
    _ = Module.finrank (ZMod 3)
          (τQ.IntertwiningMap (Representation.trivial (ZMod 3) Q (ZMod 3))) :=
      (representationDescend_head_finrank_eq π hπ τ hτ).symm
    _ = Module.finrank (ZMod 3)
          (primeActionCharacters 3 (representationGroupAction τQ)) :=
      (representationCharacterHeadEquiv τQ).finrank_eq.symm
    _ ≤ Module.finrank (ZMod 3) R.toSubmodule := hTop
    _ ≤ Module.finrank (ZMod 3) V := Submodule.finrank_le R.toSubmodule


/-- Every actual chief step inside an abelian quotient kernel costs at most
one relative ternary character once the quotient top has a sharp owner. -/
theorem ternaryChiefStep_head_le_add_weight_of_owners
    {Q : Type} [Group Q] [Finite Q]
    (π : A →* Q) (hπ : Function.Surjective π)
    (B C H : Subgroup A) [B.Normal] [C.Normal]
    (hC : C ≤ π.ker) (hKH : π.ker ≤ H)
    [IsMulCommutative π.ker]
    (a : ℕ) (step : TernaryChiefStep B C H a)
    (hOwner :
      (∃ g : Q, MulAction.IsPretransitive (Subgroup.zpowers g)
        (Q ⧸ subgroupImage π H)) ∨
      (∃ W : C1CyclicBinaryModuleOwnerWitness Q,
        Nat.card W.complement = 3)) :
    Module.finrank (ZMod 3) (primeRelativeCharacters 3 C) ≤
      Module.finrank (ZMod 3) (primeRelativeCharacters 3 B) + a := by
  cases step with
  | elementary ρ φ he hkernel =>
      have hImage := localChiefInducedImage_characterHead_le_fibre_of_owners
        π hπ C H hC hKH ρ φ he hOwner
      have hExact := localChief_head_eq H (normalChainSourceAction C) ρ φ he
      have hSource := (normalChainSourceCharactersEquiv C 3).finrank_eq
      have hRetained := localChiefRetained_le_relative C H ρ φ he
      have head_eq_of_subgroup_eq
          (D E : Subgroup A) [D.Normal] [E.Normal] (hDE : D = E) :
          Module.finrank (ZMod 3) (primeRelativeCharacters 3 D) =
            Module.finrank (ZMod 3) (primeRelativeCharacters 3 E) := by
        subst E
        rfl
      have hRetained' : Module.finrank (ZMod 3)
          (localChiefRetainedCharacters H (normalChainSourceAction C) ρ φ he) ≤
          Module.finrank (ZMod 3) (primeRelativeCharacters 3 B) :=
        hRetained.trans_eq
          (head_eq_of_subgroup_eq
            (localChiefAmbientKernel C H ρ φ he) B hkernel)
      omega
  | perfect hBC hQ =>
      letI := hQ
      have h := primeRelativeHead_chain_le B C 3 hBC
      rw [primeRelativeHead_perfect 3 (normalChainQuotient B C), Nat.add_zero] at h
      omega
  | coprime hBC q hq hQ =>
      have h := primeRelativeHead_chain_le B C 3 hBC
      rw [primeRelativeHead_power_group 3 (normalChainQuotient B C) q hq hQ,
        Nat.add_zero] at h
      omega


/-- Sharp actual-local recurrence over an abelian kernel: the whole local
chief series contributes its original ternary chief weight once, without the
usual coset-width multiplier. -/
theorem actualLocalChiefHead_le_weight_of_owners
    {R Q : Type} [Group R] [Finite R] [Group Q] [Finite Q]
    (π : A →* Q) (hπ : Function.Surjective π)
    (N H : Subgroup A) [N.Normal]
    (hN : N ≤ π.ker) (hKH : π.ker ≤ H)
    [IsMulCommutative π.ker]
    (θ : N →* R) (β : H →* R)
    (hθ : ∀ (h : H) (n : N),
      θ (MulAut.conjNormal (h : A) n) = β h * θ n * (β h)⁻¹)
    (hβ : Function.Surjective β)
    (hsep : ∀ n : N, (∀ a : A, θ (MulAut.conjNormal a n) = 1) → n = 1)
    (s : ActualChiefSeries R)
    (hOwner :
      (∃ g : Q, MulAction.IsPretransitive (Subgroup.zpowers g)
        (Q ⧸ subgroupImage π H)) ∨
      (∃ W : C1CyclicBinaryModuleOwnerWitness Q,
        Nat.card W.complement = 3)) :
    Module.finrank (ZMod 3) (primeRelativeCharacters 3 N) ≤
      actualChiefSeriesTernaryWeight s := by
  let C (i : Fin (s.length + 1)) :=
    localChiefIntersection N θ (s.subgroup i)
  let d (i : Fin (s.length + 1)) : ℕ :=
    Module.finrank (ZMod 3) (primeRelativeCharacters 3 (C i))
  let w (i : Fin s.length) : ℕ :=
    chiefTernaryWeight
      (normalChainQuotient (s.subgroup i.castSucc) (s.subgroup i.succ))
  have hC (i : Fin (s.length + 1)) : C i ≤ π.ker :=
    fun x hx => hN (localChiefIntersection_le N θ (s.subgroup i) hx)
  have hs (i : Fin s.length) : d i.succ ≤ d i.castSucc + w i := by
    exact ternaryChiefStep_head_le_add_weight_of_owners π hπ
      (C i.castSucc) (C i.succ) H (hC i.succ) hKH (w i)
      (actualLocalChiefStep N H θ β hθ hβ
        (s.subgroup i.castSucc) (s.subgroup i.succ)
        (s.step i).le (s.chief i)) hOwner
  have hsum := Finset.sum_le_sum
    (fun i (_ : i ∈ (Finset.univ : Finset (Fin s.length))) => hs i)
  have hz : C 0 = ⊥ := by
    dsimp [C]
    rw [s.head]
    exact localChiefIntersection_bot N θ hsep
  have hdz : d 0 = 0 := by
    haveI : Subsingleton (C 0) := by rw [hz]; infer_instance
    exact primeRelativeHead_perfect 3 (C 0)
  have hlast : C (Fin.last s.length) = N := by
    dsimp [C]
    rw [s.last, localChiefIntersection_top]
  have htel : d 0 + (∑ i : Fin s.length, d i.succ) =
      (∑ i : Fin s.length, d i.castSucc) + d (Fin.last s.length) := by
    exact (Fin.sum_univ_succ d).symm.trans (Fin.sum_univ_castSucc d)
  rw [hdz, zero_add] at htel
  simp only [Finset.sum_add_distrib] at hsum
  have hw : (∑ i : Fin s.length, w i) = actualChiefSeriesTernaryWeight s := by
    rfl
  have he : d (Fin.last s.length) =
      Module.finrank (ZMod 3) (primeRelativeCharacters 3 N) := by
    have head_eq_of_subgroup_eq
        (D E : Subgroup A) [D.Normal] [E.Normal] (hDE : D = E) :
        Module.finrank (ZMod 3) (primeRelativeCharacters 3 D) =
          Module.finrank (ZMod 3) (primeRelativeCharacters 3 E) := by
      subst E
      rfl
    exact head_eq_of_subgroup_eq (C (Fin.last s.length)) N hlast
  rw [he] at htel
  rw [hw] at hsum
  omega

end SymmetricSubgroupAsymptotics

end
