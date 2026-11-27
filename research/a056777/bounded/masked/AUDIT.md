# Audited standalone H1 source

The candidate is `OeisA56777.comesFromPrimeQuadruple_of_a.R2.H2.R1.H2.R1.H1.lean`.
It is 185,657 bytes, SHA-256
`b11e49f3242d2eaabf94296b3a4d6500a8b9d54a37b137a53807d187c24e7b57`.
The scoped project lint result is `lint.json`.

The checked scratch input `../MaskedAudit.lean` equals the candidate
byte-for-byte through its last line. It then adds one `#print axioms OMA.solution`
diagnostic. Lean 4.33.1 ran with `-j1 -DwarningAsError=true` and default
asynchronous elaboration. It exited successfully in 6 minutes 46 seconds.
The emitted audit is `../masked.log` and lists exactly `propext`,
`Classical.choice` and `Quot.sound` for `OMA.solution`.

The proof is the exact bounded H1 of #6850. Eight residue masks for
the moduli 7, 11, 13, 17, 19, 23, 29 and 31 are verified in the kernel.
The mask soundness theorem transfers a root to a residue root, so
using the masks cannot lose an actual candidate. This prunes 48,023
sieve-passing pairs to 2,186. The sign certificate then proves the
absence of an integer root at or below the stated upper endpoint
for every remaining pair. All p and q coverage is checked in Lean.
