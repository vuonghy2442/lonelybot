import Orig2.ForkCertBase

set_option autoImplicit false
set_option maxHeartbeats 40000000
set_option maxRecDepth 100000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-! # Cert_CrossSuit_Part4 - certificate chunks 0..272 (GENERATED)

One of 8 independent slices of the 2308-state certificate; each `decide` is
bounded by its <= 10-state chunk.  Assembled in `Orig2/ForkCertMain.lean`.
-/

namespace Cert

open EqualRung (skey skey_inj allMoves step_mem_allMoves)

set_option maxHeartbeats 40000000 in
/-- **CERTIFICATE CHUNK 0.** 10 states. -/
theorem cert_c0 : (c0.map (fun p => p.1)).all certOK = true := by decide

set_option maxHeartbeats 40000000 in
/-- **CERTIFICATE CHUNK 9.** 10 states. -/
theorem cert_c9 : (c9.map (fun p => p.1)).all certOK = true := by decide

set_option maxHeartbeats 40000000 in
/-- **CERTIFICATE CHUNK 18.** 10 states. -/
theorem cert_c18 : (c18.map (fun p => p.1)).all certOK = true := by decide

set_option maxHeartbeats 40000000 in
/-- **CERTIFICATE CHUNK 25.** 10 states. -/
theorem cert_c25 : (c25.map (fun p => p.1)).all certOK = true := by decide

set_option maxHeartbeats 40000000 in
/-- **CERTIFICATE CHUNK 35.** 10 states. -/
theorem cert_c35 : (c35.map (fun p => p.1)).all certOK = true := by decide

set_option maxHeartbeats 40000000 in
/-- **CERTIFICATE CHUNK 51.** 10 states. -/
theorem cert_c51 : (c51.map (fun p => p.1)).all certOK = true := by decide

set_option maxHeartbeats 40000000 in
/-- **CERTIFICATE CHUNK 60.** 10 states. -/
theorem cert_c60 : (c60.map (fun p => p.1)).all certOK = true := by decide

set_option maxHeartbeats 40000000 in
/-- **CERTIFICATE CHUNK 62.** 4 states. -/
theorem cert_c62 : (c62.map (fun p => p.1)).all certOK = true := by decide

set_option maxHeartbeats 40000000 in
/-- **CERTIFICATE CHUNK 63.** 10 states. -/
theorem cert_c63 : (c63.map (fun p => p.1)).all certOK = true := by decide

set_option maxHeartbeats 40000000 in
/-- **CERTIFICATE CHUNK 69.** 4 states. -/
theorem cert_c69 : (c69.map (fun p => p.1)).all certOK = true := by decide

set_option maxHeartbeats 40000000 in
/-- **CERTIFICATE CHUNK 70.** 10 states. -/
theorem cert_c70 : (c70.map (fun p => p.1)).all certOK = true := by decide

set_option maxHeartbeats 40000000 in
/-- **CERTIFICATE CHUNK 74.** 10 states. -/
theorem cert_c74 : (c74.map (fun p => p.1)).all certOK = true := by decide

set_option maxHeartbeats 40000000 in
/-- **CERTIFICATE CHUNK 77.** 10 states. -/
theorem cert_c77 : (c77.map (fun p => p.1)).all certOK = true := by decide

set_option maxHeartbeats 40000000 in
/-- **CERTIFICATE CHUNK 90.** 10 states. -/
theorem cert_c90 : (c90.map (fun p => p.1)).all certOK = true := by decide

set_option maxHeartbeats 40000000 in
/-- **CERTIFICATE CHUNK 99.** 10 states. -/
theorem cert_c99 : (c99.map (fun p => p.1)).all certOK = true := by decide

set_option maxHeartbeats 40000000 in
/-- **CERTIFICATE CHUNK 100.** 2 states. -/
theorem cert_c100 : (c100.map (fun p => p.1)).all certOK = true := by decide

set_option maxHeartbeats 40000000 in
/-- **CERTIFICATE CHUNK 101.** 10 states. -/
theorem cert_c101 : (c101.map (fun p => p.1)).all certOK = true := by decide

set_option maxHeartbeats 40000000 in
/-- **CERTIFICATE CHUNK 107.** 10 states. -/
theorem cert_c107 : (c107.map (fun p => p.1)).all certOK = true := by decide

set_option maxHeartbeats 40000000 in
/-- **CERTIFICATE CHUNK 109.** 10 states. -/
theorem cert_c109 : (c109.map (fun p => p.1)).all certOK = true := by decide

set_option maxHeartbeats 40000000 in
/-- **CERTIFICATE CHUNK 110.** 6 states. -/
theorem cert_c110 : (c110.map (fun p => p.1)).all certOK = true := by decide

set_option maxHeartbeats 40000000 in
/-- **CERTIFICATE CHUNK 116.** 6 states. -/
theorem cert_c116 : (c116.map (fun p => p.1)).all certOK = true := by decide

set_option maxHeartbeats 40000000 in
/-- **CERTIFICATE CHUNK 120.** 6 states. -/
theorem cert_c120 : (c120.map (fun p => p.1)).all certOK = true := by decide

set_option maxHeartbeats 40000000 in
/-- **CERTIFICATE CHUNK 138.** 10 states. -/
theorem cert_c138 : (c138.map (fun p => p.1)).all certOK = true := by decide

set_option maxHeartbeats 40000000 in
/-- **CERTIFICATE CHUNK 147.** 10 states. -/
theorem cert_c147 : (c147.map (fun p => p.1)).all certOK = true := by decide

set_option maxHeartbeats 40000000 in
/-- **CERTIFICATE CHUNK 154.** 10 states. -/
theorem cert_c154 : (c154.map (fun p => p.1)).all certOK = true := by decide

set_option maxHeartbeats 40000000 in
/-- **CERTIFICATE CHUNK 163.** 10 states. -/
theorem cert_c163 : (c163.map (fun p => p.1)).all certOK = true := by decide

set_option maxHeartbeats 40000000 in
/-- **CERTIFICATE CHUNK 177.** 10 states. -/
theorem cert_c177 : (c177.map (fun p => p.1)).all certOK = true := by decide

set_option maxHeartbeats 40000000 in
/-- **CERTIFICATE CHUNK 180.** 10 states. -/
theorem cert_c180 : (c180.map (fun p => p.1)).all certOK = true := by decide

set_option maxHeartbeats 40000000 in
/-- **CERTIFICATE CHUNK 189.** 10 states. -/
theorem cert_c189 : (c189.map (fun p => p.1)).all certOK = true := by decide

set_option maxHeartbeats 40000000 in
/-- **CERTIFICATE CHUNK 210.** 10 states. -/
theorem cert_c210 : (c210.map (fun p => p.1)).all certOK = true := by decide

set_option maxHeartbeats 40000000 in
/-- **CERTIFICATE CHUNK 219.** 2 states. -/
theorem cert_c219 : (c219.map (fun p => p.1)).all certOK = true := by decide

set_option maxHeartbeats 40000000 in
/-- **CERTIFICATE CHUNK 223.** 2 states. -/
theorem cert_c223 : (c223.map (fun p => p.1)).all certOK = true := by decide

set_option maxHeartbeats 40000000 in
/-- **CERTIFICATE CHUNK 263.** 4 states. -/
theorem cert_c263 : (c263.map (fun p => p.1)).all certOK = true := by decide

set_option maxHeartbeats 40000000 in
/-- **CERTIFICATE CHUNK 266.** 4 states. -/
theorem cert_c266 : (c266.map (fun p => p.1)).all certOK = true := by decide

set_option maxHeartbeats 40000000 in
/-- **CERTIFICATE CHUNK 272.** 4 states. -/
theorem cert_c272 : (c272.map (fun p => p.1)).all certOK = true := by decide

end Cert
