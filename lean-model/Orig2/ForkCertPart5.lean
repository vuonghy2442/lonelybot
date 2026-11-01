import Orig2.ForkCertBase

set_option autoImplicit false
set_option maxHeartbeats 40000000
set_option maxRecDepth 100000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-! # Cert_CrossSuit_Part5 - certificate chunks 1..273 (GENERATED)

One of 8 independent slices of the 2308-state certificate; each `decide` is
bounded by its <= 10-state chunk.  Assembled in `Orig2/ForkCertMain.lean`.
-/

namespace Cert

open EqualRung (skey skey_inj allMoves step_mem_allMoves)

set_option maxHeartbeats 40000000 in
/-- **CERTIFICATE CHUNK 1.** 10 states. -/
theorem cert_c1 : (c1.map (fun p => p.1)).all certOK = true := by decide

set_option maxHeartbeats 40000000 in
/-- **CERTIFICATE CHUNK 10.** 10 states. -/
theorem cert_c10 : (c10.map (fun p => p.1)).all certOK = true := by decide

set_option maxHeartbeats 40000000 in
/-- **CERTIFICATE CHUNK 19.** 10 states. -/
theorem cert_c19 : (c19.map (fun p => p.1)).all certOK = true := by decide

set_option maxHeartbeats 40000000 in
/-- **CERTIFICATE CHUNK 26.** 10 states. -/
theorem cert_c26 : (c26.map (fun p => p.1)).all certOK = true := by decide

set_option maxHeartbeats 40000000 in
/-- **CERTIFICATE CHUNK 36.** 10 states. -/
theorem cert_c36 : (c36.map (fun p => p.1)).all certOK = true := by decide

set_option maxHeartbeats 40000000 in
/-- **CERTIFICATE CHUNK 52.** 10 states. -/
theorem cert_c52 : (c52.map (fun p => p.1)).all certOK = true := by decide

set_option maxHeartbeats 40000000 in
/-- **CERTIFICATE CHUNK 61.** 10 states. -/
theorem cert_c61 : (c61.map (fun p => p.1)).all certOK = true := by decide

set_option maxHeartbeats 40000000 in
/-- **CERTIFICATE CHUNK 64.** 10 states. -/
theorem cert_c64 : (c64.map (fun p => p.1)).all certOK = true := by decide

set_option maxHeartbeats 40000000 in
/-- **CERTIFICATE CHUNK 71.** 10 states. -/
theorem cert_c71 : (c71.map (fun p => p.1)).all certOK = true := by decide

set_option maxHeartbeats 40000000 in
/-- **CERTIFICATE CHUNK 75.** 10 states. -/
theorem cert_c75 : (c75.map (fun p => p.1)).all certOK = true := by decide

set_option maxHeartbeats 40000000 in
/-- **CERTIFICATE CHUNK 78.** 10 states. -/
theorem cert_c78 : (c78.map (fun p => p.1)).all certOK = true := by decide

set_option maxHeartbeats 40000000 in
/-- **CERTIFICATE CHUNK 91.** 10 states. -/
theorem cert_c91 : (c91.map (fun p => p.1)).all certOK = true := by decide

set_option maxHeartbeats 40000000 in
/-- **CERTIFICATE CHUNK 102.** 10 states. -/
theorem cert_c102 : (c102.map (fun p => p.1)).all certOK = true := by decide

set_option maxHeartbeats 40000000 in
/-- **CERTIFICATE CHUNK 108.** 6 states. -/
theorem cert_c108 : (c108.map (fun p => p.1)).all certOK = true := by decide

set_option maxHeartbeats 40000000 in
/-- **CERTIFICATE CHUNK 111.** 10 states. -/
theorem cert_c111 : (c111.map (fun p => p.1)).all certOK = true := by decide

set_option maxHeartbeats 40000000 in
/-- **CERTIFICATE CHUNK 122.** 6 states. -/
theorem cert_c122 : (c122.map (fun p => p.1)).all certOK = true := by decide

set_option maxHeartbeats 40000000 in
/-- **CERTIFICATE CHUNK 125.** 8 states. -/
theorem cert_c125 : (c125.map (fun p => p.1)).all certOK = true := by decide

set_option maxHeartbeats 40000000 in
/-- **CERTIFICATE CHUNK 137.** 4 states. -/
theorem cert_c137 : (c137.map (fun p => p.1)).all certOK = true := by decide

set_option maxHeartbeats 40000000 in
/-- **CERTIFICATE CHUNK 139.** 10 states. -/
theorem cert_c139 : (c139.map (fun p => p.1)).all certOK = true := by decide

set_option maxHeartbeats 40000000 in
/-- **CERTIFICATE CHUNK 148.** 10 states. -/
theorem cert_c148 : (c148.map (fun p => p.1)).all certOK = true := by decide

set_option maxHeartbeats 40000000 in
/-- **CERTIFICATE CHUNK 155.** 10 states. -/
theorem cert_c155 : (c155.map (fun p => p.1)).all certOK = true := by decide

set_option maxHeartbeats 40000000 in
/-- **CERTIFICATE CHUNK 158.** 4 states. -/
theorem cert_c158 : (c158.map (fun p => p.1)).all certOK = true := by decide

set_option maxHeartbeats 40000000 in
/-- **CERTIFICATE CHUNK 164.** 10 states. -/
theorem cert_c164 : (c164.map (fun p => p.1)).all certOK = true := by decide

set_option maxHeartbeats 40000000 in
/-- **CERTIFICATE CHUNK 178.** 10 states. -/
theorem cert_c178 : (c178.map (fun p => p.1)).all certOK = true := by decide

set_option maxHeartbeats 40000000 in
/-- **CERTIFICATE CHUNK 181.** 10 states. -/
theorem cert_c181 : (c181.map (fun p => p.1)).all certOK = true := by decide

set_option maxHeartbeats 40000000 in
/-- **CERTIFICATE CHUNK 190.** 10 states. -/
theorem cert_c190 : (c190.map (fun p => p.1)).all certOK = true := by decide

set_option maxHeartbeats 40000000 in
/-- **CERTIFICATE CHUNK 224.** 10 states. -/
theorem cert_c224 : (c224.map (fun p => p.1)).all certOK = true := by decide

set_option maxHeartbeats 40000000 in
/-- **CERTIFICATE CHUNK 228.** 10 states. -/
theorem cert_c228 : (c228.map (fun p => p.1)).all certOK = true := by decide

set_option maxHeartbeats 40000000 in
/-- **CERTIFICATE CHUNK 240.** 10 states. -/
theorem cert_c240 : (c240.map (fun p => p.1)).all certOK = true := by decide

set_option maxHeartbeats 40000000 in
/-- **CERTIFICATE CHUNK 241.** 6 states. -/
theorem cert_c241 : (c241.map (fun p => p.1)).all certOK = true := by decide

set_option maxHeartbeats 40000000 in
/-- **CERTIFICATE CHUNK 245.** 6 states. -/
theorem cert_c245 : (c245.map (fun p => p.1)).all certOK = true := by decide

set_option maxHeartbeats 40000000 in
/-- **CERTIFICATE CHUNK 258.** 8 states. -/
theorem cert_c258 : (c258.map (fun p => p.1)).all certOK = true := by decide

set_option maxHeartbeats 40000000 in
/-- **CERTIFICATE CHUNK 260.** 8 states. -/
theorem cert_c260 : (c260.map (fun p => p.1)).all certOK = true := by decide

set_option maxHeartbeats 40000000 in
/-- **CERTIFICATE CHUNK 273.** 2 states. -/
theorem cert_c273 : (c273.map (fun p => p.1)).all certOK = true := by decide

end Cert
