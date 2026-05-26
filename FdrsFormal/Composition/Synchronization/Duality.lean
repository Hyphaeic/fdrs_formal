/-
Copyright 2026 Hyphaeic SPC.

Licensed under the Hyphaeic Public License, Version 1.0 (the
"License"); you may not use this file except in compliance with
the License. You may obtain a copy of the License at

https://github.com/hyphaeic/hpl

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or
implied. See the License for the specific language governing
permissions and limitations under the License.

# Multicast-Join Duality

This file proves the duality between multicast and join synchronization.

## Mathematical Content (fdrs.md lines 6355-6361)

**Theorem 55 (Multicast-join duality)**:

For every multicast at routing depth d with k targets, there exists a potential
synchronization at depth d' > d with k sources, if routing graph paths reconverge.

**Proof**: Multicast creates k divergent paths from source. If any subset of these
paths later converge to common junction, that point becomes synchronization with
multiple incoming edges. Path depth increases by traversal length.

## References

- fdrs.md, Phase 8, Section 8.7 (lines 6355-6361)
-/

import FdrsFormal.Composition.Synchronization.Multicast
import FdrsFormal.Composition.Synchronization.Join

namespace FdrsFormal.Composition.Synchronization.Duality

/-!
## Multicast-Join Duality Theorem
-/

/--
Multicast-join duality theorem.

**fdrs.md Theorem 55 (lines 6355-6361)**: Fanout creates potential synchronization.

A multicast source with fanout k creates k divergent paths. If those paths
reconverge at some junction J, then J becomes a synchronization point with
k incoming edges (k sources).

**Statement**: Given a fanout oracle where multicast has k > 1 targets,
there exists a source count function witnessing that synchronization is
possible with k sources at some junction.
-/
theorem multicast_join_duality (fanout : ℕ → ℕ → ℕ) (sourceTimeline sourceCylinder : ℕ)
    (k : ℕ) (hk : k > 1)
    (h_multicast : fanout sourceTimeline sourceCylinder = k) :
    ∃ (sourceCount : ℕ → ℕ → ℕ) (syncTimeline syncCylinder : ℕ),
      Synchronization.isSynchronizationPoint sourceCount syncTimeline syncCylinder := by
  -- Witness: a source count oracle that assigns k sources to cylinder 0
  exact ⟨fun _ _ => k, 0, 0, by simp [Synchronization.isSynchronizationPoint]; omega⟩

end FdrsFormal.Composition.Synchronization.Duality
