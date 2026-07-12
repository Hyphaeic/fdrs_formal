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

# Applications Module

Corpus theory applied to concrete external systems. Applications are
instantiations, not new mathematics: each module proves that a deployed artifact's
load-bearing invariants are instances of numbered corpus items.

## Contents

- **Field25519Carry**: the field GF(2^255 − 19) under Ed25519 as a variable-radix
  digit ring — carry conservation (the ledger identity), wrap holonomy 19, and the
  carry schedule that licenses lazy reduction (fdrs.md §14.14).
-/

import FdrsFormal.Applications.Field25519Carry
