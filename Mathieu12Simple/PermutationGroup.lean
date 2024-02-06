import Mathlib.GroupTheory.Perm.Basic
import Mathlib.GroupTheory.Subgroup.Simple
import Mathlib.Tactic

namespace fin_up_down
variable {n:ℕ} {m:Fin (n+1)}
end fin_up_down

open Subgroup






def map_stabiliser_to_permutegroup: MulAction.stabilizer (Equiv.Perm (Fin (n+1))) (m: Fin (n+1)) → Equiv.Perm (Fin n) :=
  fun ⟨σ,hsigma_in_stabiliser⟩ => {
    toFun :=fun x_fin => by

      have x_m_cases : x_fin < (m:ℕ) ∨ x_fin = (m:ℕ) ∨ x_fin > (m:ℕ)
      . exact Nat.lt_trichotomy ↑x_fin ↑m
      apply Or.by_cases x_m_cases
      .


    invFun := sorry
    left_inv := sorry
    right_inv := sorry
  }
