"""Write bounded Lean kernel computations for normalized code 157."""
from pathlib import Path

CHUNK = 32
BLOCKS = 1024 // CHUNK

def emit(path, indices):
    lines = [
        "import Bounds",
        "namespace Erdos1082",
        "set_option maxRecDepth 100000",
        "set_option maxHeartbeats 0",
    ]
    for j in indices:
        lines += [
            f"theorem checked157_{j} : checkBlock157 {CHUNK * j} {CHUNK} = true := by",
            "  decide +kernel",
        ]
    lines.append("end Erdos1082")
    Path(path).write_text("\n".join(lines) + "\n")

emit("Checked157_0.lean", range(4))
for group in range(1, 8):
    modules = []
    for j in range(4 * group, 4 * group + 4):
        module = f"Check157Block{j:02d}"
        emit(f"{module}.lean", [j])
        modules.append(module)
    Path(f"Checked157_{group}.lean").write_text(
        "\n".join(f"import {module}" for module in modules) + "\n"
    )
