import SymmetricSubgroupAsymptotics.CFSGHermitianMaximalExchange
import Mathlib.Logic.Relation

/-! The actual maximal-isotropic gallery is connected. Each step
loses at most one intersection dimension; induction strictly increases
intersection with the target. No building or polar-space recognition
theorem is supplied as an assumption. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGHermitianOrthogonalSpan
variable {K I : Type*} [Field K] [Fintype I]
variable (sigma : K ≃+* K) (H : Matrix I I K)

def MaximalSpace := {S : Submodule K (I → K) // MaximalIsotropic sigma H S}

def GalleryStep (S T : MaximalSpace sigma H) : Prop :=
  Module.finrank K S.val ≤ Module.finrank K ↥(S.val ⊓ T.val) + 1

theorem maximal_gallery_connected
    (hswap : ∀ x y, CFSGTwistedAUnitaryParameters.hermitianPair sigma H x y = 0 ↔
      CFSGTwistedAUnitaryParameters.hermitianPair sigma H y x = 0)
    (S T : MaximalSpace sigma H) : Relation.ReflTransGen (GalleryStep sigma H) S T := by
  suffices hall : ∀ n, ∀ S : MaximalSpace sigma H,
      Module.finrank K T.val - Module.finrank K ↥(S.val ⊓ T.val) = n →
        Relation.ReflTransGen (GalleryStep sigma H) S T by
    exact hall _ S rfl
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro S hn
    by_cases he : S = T
    · subst S
      exact Relation.ReflTransGen.refl
    · have hnot : ¬ T.val ≤ S.val := by
        intro h
        have heq := T.property.2 S.val S.property.1 h
        exact he (Subtype.ext heq)
      obtain ⟨y, hyT, hyS⟩ := Set.not_subset.mp hnot
      obtain ⟨M, hM, hadj, hgain⟩ := maximal_exchange_towards sigma H S.val T.val
        S.property T.property hswap y hyT hyS
      let R : MaximalSpace sigma H := ⟨M, hM⟩
      have hstep : GalleryStep sigma H S R := hadj
      have hltcap := Submodule.finrank_lt_finrank_of_lt hgain
      have hcap := Submodule.finrank_mono (inf_le_right : M ⊓ T.val ≤ T.val)
      have hlt : Module.finrank K T.val - Module.finrank K ↥(M ⊓ T.val) < n := by
        rw [← hn]
        omega
      exact (Relation.ReflTransGen.single hstep).trans (ih _ hlt R rfl)

end SymmetricSubgroupAsymptotics.CFSGHermitianOrthogonalSpan
