/-
Embedding R ↪ R̂

Embeds eventually-zero sequences into the full product space.
-/

import FdrsFormal.Core.Infinite.DirectLimit

namespace FdrsFormal.Core.Infinite

open FdrsFormal.Core.Primitives FdrsFormal.Core.Finite

/-- Natural embedding: R^(∞)_fin ↪ R̂ -/
def DirectLimitSpace.embed (b : RadixSeq) (τ : DirectLimitSpace b) : CompletedSpace b :=
  τ.digits

theorem embed_injective (b : RadixSeq) : Function.Injective (DirectLimitSpace.embed b) := by
  intro τ σ h
  ext i
  unfold DirectLimitSpace.embed at h
  simp [congrFun h i]

/-
Note: The density theorem (R is dense in R̂) belongs in the Topology module
since it requires a TopologicalSpace instance on CompletedSpace.
-/

end FdrsFormal.Core.Infinite
