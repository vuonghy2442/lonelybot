import Orig2.ForkCertBase

set_option autoImplicit false
set_option maxHeartbeats 40000000
set_option maxRecDepth 100000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-! # Cert_CrossSuit_Part1 - certificate chunks 5..268 (GENERATED)

One of 8 independent slices of the 2308-state certificate; each `decide` is
bounded by its <= 10-state chunk.  Assembled in `Orig2/ForkCertMain.lean`.
-/

namespace Cert

open EqualRung (skey skey_inj allMoves step_mem_allMoves)

set_option maxHeartbeats 40000000 in
/-- **CERTIFICATE CHUNK 5.** 10 states. -/
theorem cert_c5 : (c5.map (fun p => p.1)).all certOK = true := by decide

set_option maxHeartbeats 40000000 in
/-- **CERTIFICATE CHUNK 13.** 4 states. -/
theorem cert_c13 : (c13.map (fun p => p.1)).all certOK = true := by decide

set_option maxHeartbeats 40000000 in
/-- **CERTIFICATE CHUNK 15.** 10 states. -/
theorem cert_c15 : (c15.map (fun p => p.1)).all certOK = true := by decide

set_option maxHeartbeats 40000000 in
/-- **CERTIFICATE CHUNK 22.** 10 states. -/
theorem cert_c22 : (c22.map (fun p => p.1)).all certOK = true := by decide

set_option maxHeartbeats 40000000 in
/-- **CERTIFICATE CHUNK 31.** 10 states. -/
theorem cert_c31 : (c31.map (fun p => p.1)).all certOK = true := by decide

set_option maxHeartbeats 40000000 in
/-- **CERTIFICATE CHUNK 34.** 4 states. -/
theorem cert_c34 : (c34.map (fun p => p.1)).all certOK = true := by decide

set_option maxHeartbeats 40000000 in
/-- **CERTIFICATE CHUNK 40.** 10 states. -/
theorem cert_c40 : (c40.map (fun p => p.1)).all certOK = true := by decide

set_option maxHeartbeats 40000000 in
/-- **CERTIFICATE CHUNK 45.** 10 states. -/
theorem cert_c45 : (c45.map (fun p => p.1)).all certOK = true := by decide

set_option maxHeartbeats 40000000 in
/-- **CERTIFICATE CHUNK 57.** 10 states. -/
theorem cert_c57 : (c57.map (fun p => p.1)).all certOK = true := by decide

set_option maxHeartbeats 40000000 in
/-- **CERTIFICATE CHUNK 68.** 10 states. -/
theorem cert_c68 : (c68.map (fun p => p.1)).all certOK = true := by decide

set_option maxHeartbeats 40000000 in
/-- **CERTIFICATE CHUNK 80.** 2 states. -/
theorem cert_c80 : (c80.map (fun p => p.1)).all certOK = true := by decide

set_option maxHeartbeats 40000000 in
/-- **CERTIFICATE CHUNK 82.** 10 states. -/
theorem cert_c82 : (c82.map (fun p => p.1)).all certOK = true := by decide

set_option maxHeartbeats 40000000 in
/-- **CERTIFICATE CHUNK 86.** 10 states. -/
theorem cert_c86 : (c86.map (fun p => p.1)).all certOK = true := by decide

set_option maxHeartbeats 40000000 in
/-- **CERTIFICATE CHUNK 88.** 2 states. -/
theorem cert_c88 : (c88.map (fun p => p.1)).all certOK = true := by decide

set_option maxHeartbeats 40000000 in
/-- **CERTIFICATE CHUNK 95.** 10 states. -/
theorem cert_c95 : (c95.map (fun p => p.1)).all certOK = true := by decide

set_option maxHeartbeats 40000000 in
/-- **CERTIFICATE CHUNK 118.** 6 states. -/
theorem cert_c118 : (c118.map (fun p => p.1)).all certOK = true := by decide

set_option maxHeartbeats 40000000 in
/-- **CERTIFICATE CHUNK 134.** 10 states. -/
theorem cert_c134 : (c134.map (fun p => p.1)).all certOK = true := by decide

set_option maxHeartbeats 40000000 in
/-- **CERTIFICATE CHUNK 143.** 10 states. -/
theorem cert_c143 : (c143.map (fun p => p.1)).all certOK = true := by decide

set_option maxHeartbeats 40000000 in
/-- **CERTIFICATE CHUNK 160.** 10 states. -/
theorem cert_c160 : (c160.map (fun p => p.1)).all certOK = true := by decide

set_option maxHeartbeats 40000000 in
/-- **CERTIFICATE CHUNK 169.** 10 states. -/
theorem cert_c169 : (c169.map (fun p => p.1)).all certOK = true := by decide

set_option maxHeartbeats 40000000 in
/-- **CERTIFICATE CHUNK 172.** 4 states. -/
theorem cert_c172 : (c172.map (fun p => p.1)).all certOK = true := by decide

set_option maxHeartbeats 40000000 in
/-- **CERTIFICATE CHUNK 174.** 10 states. -/
theorem cert_c174 : (c174.map (fun p => p.1)).all certOK = true := by decide

set_option maxHeartbeats 40000000 in
/-- **CERTIFICATE CHUNK 185.** 10 states. -/
theorem cert_c185 : (c185.map (fun p => p.1)).all certOK = true := by decide

set_option maxHeartbeats 40000000 in
/-- **CERTIFICATE CHUNK 197.** 10 states. -/
theorem cert_c197 : (c197.map (fun p => p.1)).all certOK = true := by decide

set_option maxHeartbeats 40000000 in
/-- **CERTIFICATE CHUNK 204.** 10 states. -/
theorem cert_c204 : (c204.map (fun p => p.1)).all certOK = true := by decide

set_option maxHeartbeats 40000000 in
/-- **CERTIFICATE CHUNK 215.** 2 states. -/
theorem cert_c215 : (c215.map (fun p => p.1)).all certOK = true := by decide

set_option maxHeartbeats 40000000 in
/-- **CERTIFICATE CHUNK 218.** 10 states. -/
theorem cert_c218 : (c218.map (fun p => p.1)).all certOK = true := by decide

set_option maxHeartbeats 40000000 in
/-- **CERTIFICATE CHUNK 220.** 10 states. -/
theorem cert_c220 : (c220.map (fun p => p.1)).all certOK = true := by decide

set_option maxHeartbeats 40000000 in
/-- **CERTIFICATE CHUNK 227.** 2 states. -/
theorem cert_c227 : (c227.map (fun p => p.1)).all certOK = true := by decide

set_option maxHeartbeats 40000000 in
/-- **CERTIFICATE CHUNK 234.** 10 states. -/
theorem cert_c234 : (c234.map (fun p => p.1)).all certOK = true := by decide

set_option maxHeartbeats 40000000 in
/-- **CERTIFICATE CHUNK 242.** 10 states. -/
theorem cert_c242 : (c242.map (fun p => p.1)).all certOK = true := by decide

set_option maxHeartbeats 40000000 in
/-- **CERTIFICATE CHUNK 243.** 6 states. -/
theorem cert_c243 : (c243.map (fun p => p.1)).all certOK = true := by decide

set_option maxHeartbeats 40000000 in
/-- **CERTIFICATE CHUNK 244.** 10 states. -/
theorem cert_c244 : (c244.map (fun p => p.1)).all certOK = true := by decide

set_option maxHeartbeats 40000000 in
/-- **CERTIFICATE CHUNK 268.** 2 states. -/
theorem cert_c268 : (c268.map (fun p => p.1)).all certOK = true := by decide

end Cert
