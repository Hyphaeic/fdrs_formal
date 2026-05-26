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

# Composition Module

This module aggregates all composition components for building
and analyzing composed FDRS programs.

## Contents

- **TimelineGraphs**: Timeline graph structure for program visualization
- **Routing**: Data flow and routing analysis
- **DeadlockAnalysis**: Deadlock detection and prevention
- **TimingBounds**: Timing analysis and schedulability
- **Junctions**: Junction types and transfer semantics (Phase 8.1-8.2)
- **Injection**: Injection operations and locality (Phase 8.3)
- **Lifecycle**: Spawn/terminate dynamics (Phase 8.6)
- **Synchronization**: Multicast and join patterns (Phase 8.7)
- **Verification**: Compile-time verification (Phase 8.8)
- **ObserverIntegration**: Routed observer complex (Phase 8.9)

## References

- fdrs.md, Phase 8 (Composition - basic)
- fdrs.md, Phase 8 (Multi-Timeline Routing - advanced, lines 5899-6548)
-/

import FdrsFormal.Composition.TimelineGraphs.Definition
import FdrsFormal.Composition.TimelineGraphs.Identifiers
import FdrsFormal.Composition.Routing.Definition
import FdrsFormal.Composition.Routing.Events
import FdrsFormal.Composition.DeadlockAnalysis.Definition
import FdrsFormal.Composition.TimingBounds.Definition
import FdrsFormal.Composition.TimingBounds.RoutingAnalysis

-- Phase 8 advanced content
import FdrsFormal.Composition.Junctions
import FdrsFormal.Composition.Injection
import FdrsFormal.Composition.Lifecycle
import FdrsFormal.Composition.Synchronization
import FdrsFormal.Composition.Verification
import FdrsFormal.Composition.ObserverIntegration
