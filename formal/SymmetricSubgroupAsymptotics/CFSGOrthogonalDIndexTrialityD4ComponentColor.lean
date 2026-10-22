import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexSingularComponents

/-! An isometry in the genuine even-intersection component preserves
intersection parity relative to EVERY maximal singular reference space.
This is a direct consequence of the proved quadratic triangle parity. -/
set_option autoImplicit false
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTrialityD4ComponentColor
open CFSGOrthogonalDIndexSingularComponents CFSGOrthogonalDIndexSingularParity
open CFSGOrthogonalDIndexSingularTransport
variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]

theorem component_preserves_all_reference_parities (Q : QuadraticForm K V)
    (hQ : Q.polarBilin.Nondegenerate) (r : ℕ) (hV : Module.finrank K V = 2 * r)
    (P B M : Submodule K V)
    (hP : LinearMap.BilinForm.orthogonal Q.polarBilin P = P)
    (hB : LinearMap.BilinForm.orthogonal Q.polarBilin B = B)
    (hM : LinearMap.BilinForm.orthogonal Q.polarBilin M = M)
    (hzP : ∀ x : P, Q (x : V) = 0) (hzB : ∀ x : B, Q (x : V) = 0)
    (hzM : ∀ x : M, Q (x : V) = 0)
    (f : V ≃ₗ[K] V) (hf : ∀ x, Q (f x) = Q x)
    (hcomponent : Even (distance r P (P.map f.toLinearMap))) :
    distance r B (M.map f.toLinearMap) % 2 = distance r B M % 2 := by
  let Pf := P.map f.toLinearMap
  let Mf := M.map f.toLinearMap
  have hPf := map_self_orthogonal Q f hf P hP
  have hMf := map_self_orthogonal Q f hf M hM
  have hzPf := map_singular Q f hf P hzP
  have hzMf := map_singular Q f hf M hzM
  have ht0 := even_three_distances Q hQ r hV P Pf Mf hP hPf hMf hzP hzPf hzMf
  have ht1 := even_three_distances Q hQ r hV P B M hP hB hM hzP hzB hzM
  have ht2 := even_three_distances Q hQ r hV P B Mf hP hB hMf hzP hzB hzMf
  have hd : distance r Pf Mf = distance r P M :=
    congrArg (fun n : ℕ => r - n) (intersection_map_finrank f P M)
  change Even (distance r P Pf + distance r Pf Mf + distance r P Mf) at ht0
  change Even (distance r P B + distance r B M + distance r P M) at ht1
  change Even (distance r P B + distance r B Mf + distance r P Mf) at ht2
  rw [hd] at ht0
  rw [Nat.even_iff] at ht0 ht1 ht2 hcomponent
  change (distance r P Pf) % 2 = 0 at hcomponent
  change distance r B Mf % 2 = distance r B M % 2
  omega

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTrialityD4ComponentColor
