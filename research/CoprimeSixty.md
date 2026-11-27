# A Lean proof of the coprime 60-denominator bound

Any witness for the unit-free coprime variant of Erdős Problem 307 uses at least 60 distinct denominators. The proof combines a least-prime-factor bound for witnesses containing a composite with Vico Bonfioli's kernel-checked prime-only theorem. Bonfioli already states the coprime result in his paper.

The patch adapts the imports and prime-counting API in Bonfioli's Lean sources for the Formal Conjectures Lean v4.33.1 environment. Bonfioli's MIT license is included in BONFIOLI-LICENSE.txt and remains in the external checkout. Lean's kernel evaluates the level-59 search using decide +kernel, which avoids a duplicate reduction in the elaborator.

## Reproduce

Use Formal Conjectures commit 9097e2f90e66d2f6244209cb1c07f7120d17ec53 with its Mathlib cache and Lean v4.33.1. Only the imports selected by the patch need cached modules. Run these commands from this folder.

    git clone --depth 1 --branch v1.76.2 https://github.com/ElVec1o/erdos307.git
    git -C erdos307 apply "$PWD/bonfioli-v1.76.2-lean-v4.33.1.patch"
    OMA_FC=/path/to/formal-conjectures bash ./check-coprime-sixty.sh ./erdos307

The script compiles the required modules in a temporary directory and prints the axioms of the resulting theorem. The Bonfioli checkout must be at commit 36c3b7979a77e003fcf47016e41f2f7133495415.
