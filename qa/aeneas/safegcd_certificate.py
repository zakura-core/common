#!/usr/bin/env python3
"""Generate untrusted hull data and kernel-checked divstep certificate modules."""

import argparse
from dataclasses import dataclass
import hashlib
import json
from pathlib import Path
import time


BOUND = 1 << 255
PRECISION = 6
LAST_STEP = 732


@dataclass(frozen=True)
class Node:
    delta: int
    shift_x: int
    shift_y: int
    compact: tuple[tuple[int, int], ...]
    terminal: bool

    def vertices(self):
        return tuple((x << self.shift_x, y << self.shift_y) for x, y in self.compact)


def orientation(a, b, p):
    return (b[0] - a[0]) * (p[1] - a[1]) - (b[1] - a[1]) * (p[0] - a[0])


def convex_hull(points):
    points = sorted(set(points))
    if len(points) < 2:
        return tuple(points)

    def boundary(sequence):
        result = []
        for point in sequence:
            while len(result) > 1 and orientation(result[-2], result[-1], point) <= 0:
                result.pop()
            result.append(point)
        return result

    return tuple(boundary(points)[:-1] + boundary(reversed(points))[:-1])


def rounded_node(delta, points, step):
    shift_x = max(0, max(abs(x) for x, _ in points).bit_length() - PRECISION)
    shift_y = max(0, max(abs(y) for _, y in points).bit_length() - PRECISION)
    width_x, width_y = 1 << shift_x, 1 << shift_y
    corners = []
    for x, y in points:
        low_x, high_x = x // width_x, -((-x) // width_x)
        low_y, high_y = y // width_y, -((-y) // width_y)
        corners.extend(((low_x, low_y), (low_x, high_y), (high_x, low_y), (high_x, high_y)))
    compact = convex_hull(corners)
    terminal = all(abs(y << shift_y) * BOUND < 1 << step for _, y in compact)
    return Node(delta, shift_x, shift_y, compact, terminal)


def transform(branch, point):
    x, y = point
    if branch == "swap":
        return 2 * y, y - x
    if branch == "add":
        return 2 * x, y + x
    return 2 * x, y


def next_delta(delta, branch):
    return 1 - delta if branch == "swap" else delta + 1


def generate_stages():
    stages = [[Node(1, 0, 0, ((1, 0), (1, 1)), False)]]
    active = stages[0]
    for step in range(1, LAST_STEP + 1):
        candidates = {}
        for node in active:
            for branch in ("even", "swap" if node.delta > 0 else "add"):
                destination = next_delta(node.delta, branch)
                candidates.setdefault(destination, []).extend(
                    transform(branch, vertex) for vertex in node.vertices()
                )
        nodes = [
            rounded_node(delta, convex_hull(points), step)
            for delta, points in sorted(candidates.items())
        ]
        stages.append(nodes)
        active = [node for node in nodes if not node.terminal]
        if not active:
            if step != LAST_STEP:
                raise RuntimeError(f"Unexpected terminal stage: {step}")
            return stages
    raise RuntimeError("The untrusted hull generator did not reach the required terminal stage")


def containing_triangle(vertices, point):
    if len(vertices) < 3:
        return 0
    low, high = 1, len(vertices) - 1
    while high > low + 1:
        middle = (low + high) // 2
        if orientation(vertices[0], vertices[middle], point) >= 0:
            low = middle
        else:
            high = middle
    a, b, c = vertices[0], vertices[low], vertices[low + 1]
    if not (
        orientation(a, b, c) > 0
        and orientation(b, c, point) >= 0
        and orientation(c, a, point) >= 0
        and orientation(a, b, point) >= 0
    ):
        raise RuntimeError("The untrusted search failed to find a containing triangle")
    return low


def branch_witness(source, target, branch):
    if source.terminal:
        return "⟨0, []⟩"
    destination = next_delta(source.delta, branch)
    index = next(i for i, node in enumerate(target) if node.delta == destination)
    vertices = target[index].vertices()
    triangles = [
        containing_triangle(vertices, transform(branch, vertex))
        for vertex in source.vertices()
    ]
    return "⟨" + str(index) + ", [" + ", ".join(map(str, triangles)) + "]⟩"


def stage_name(step):
    return f"stage{step:03}"


def node_name(step, index):
    return f"{stage_name(step)}_node{index:03}"


HEADER = """namespace UdonVerify.SafeGcd.Cert255
set_option maxHeartbeats 100000000
set_option maxRecDepth 100000
set_option exponentiation.threshold 1024
"""


def data_source(step, nodes):
    imports = "import DivstepsCertificate\n" if step == 0 else "import DivstepsWitnessCheck\n"
    lines = [imports, HEADER]
    if step == 0:
        lines.extend([
            f"def {node_name(0, 0)} : Node := initialNode\n",
            f"def {stage_name(0)} : Nodes := initialNodes\n",
        ])
    else:
        for index, node in enumerate(nodes):
            vertices = ", ".join(f"⟨{x}, {y}⟩" for x, y in node.compact)
            terminal = "true" if node.terminal else "false"
            lines.append(
                f"def {node_name(step, index)} : Node := "
                f"⟨{node.delta}, {1 << node.shift_x}, {1 << node.shift_y}, #[{vertices}], {terminal}⟩\n"
            )
        names = ", ".join(node_name(step, index) for index in range(len(nodes)))
        lines.append(f"def {stage_name(step)} : Nodes := #[{names}]\n")
    return "".join(lines) + "end UdonVerify.SafeGcd.Cert255\n"


def check_source(step, source, target):
    prefix = stage_name(step)
    target_name, source_name = stage_name(step), stage_name(step - 1)
    lines = [
        f"import Divsteps255Data.Stage{step - 1:03}\n",
        f"import Divsteps255Data.Stage{step:03}\n",
        HEADER,
    ]
    for index, node in enumerate(source):
        even = branch_witness(node, target, "even")
        odd = branch_witness(node, target, "swap" if node.delta > 0 else "add")
        lines.append(
            f"def {prefix}_witness{index:03} : BranchWitness × BranchWitness := ({even}, {odd})\n"
        )
        lines.append(
            f"theorem {prefix}_head{index:03} : nodeWitnessCheck {target_name} "
            f"{node_name(step - 1, index)} {prefix}_witness{index:03} = true := by decide +kernel\n"
        )
    names = ", ".join(f"{prefix}_witness{index:03}" for index in range(len(source)))
    lines.append(f"def {prefix}_witnesses : List (BranchWitness × BranchWitness) := [{names}]\n")
    lines.append(
        f"theorem {prefix}_terminal : {target_name}.toList.all "
        f"(terminalCheck {BOUND} {1 << step}) = true := by decide +kernel\n"
    )
    proof = f"source_witness_check_nil {target_name}"
    for index in reversed(range(len(source))):
        proof = (
            f"source_witness_check_cons {target_name} {node_name(step - 1, index)} _ "
            f"{prefix}_witness{index:03} _ {prefix}_head{index:03} ({proof})"
        )
    lines.append(
        f"theorem {prefix}_source : sourceWitnessCheck {target_name} {source_name}.toList "
        f"{prefix}_witnesses = true := by\n  exact {proof}\n"
    )
    lines.append(
        f"theorem {prefix}_checked : stepWitnessCheck {BOUND} {1 << step} "
        f"{source_name} {target_name} {prefix}_witnesses = true :=\n"
        f"  step_witness_check_intro _ _ _ _ _ {prefix}_terminal {prefix}_source\n"
    )
    lines.append(
        f"theorem {prefix}_valid : StepValid (2 ^ 255) (2 ^ {step}) "
        f"{source_name} {target_name} :=\n"
        f"  step_witness_check_sound _ _ _ _ _ {prefix}_checked\n"
    )
    return "".join(lines) + "end UdonVerify.SafeGcd.Cert255\n"


def write_modules(output, stages):
    data_directory = output / "Divsteps255Data"
    check_directory = output / "Divsteps255Checks"
    data_directory.mkdir()
    check_directory.mkdir()
    paths = []

    def write(path, source):
        path.write_text(source)
        paths.append(path)

    for step, nodes in enumerate(stages):
        write(data_directory / f"Stage{step:03}.lean", data_source(step, nodes))
        if step:
            write(check_directory / f"Stage{step:03}.lean", check_source(step, stages[step - 1], nodes))
    data_root = "".join(f"import Divsteps255Data.Stage{step:03}\n" for step in range(len(stages)))
    data_root += HEADER
    names = ", ".join(stage_name(step) for step in range(len(stages)))
    data_root += f"def stages (n : Nat) : Nodes := (#[{names}] : _root_.Array Nodes)[n]!\n"
    data_root += "end UdonVerify.SafeGcd.Cert255\n"
    write(output / "Divsteps255Data.lean", data_root)
    checks_root = "".join(f"import Divsteps255Checks.Stage{step:03}\n" for step in range(1, len(stages)))
    checks_root += HEADER
    checks_root += "theorem all_steps_valid (n : Nat) (hn : n < 732) :\n"
    checks_root += "    StepValid (2 ^ 255) (2 ^ (n + 1)) (stages n) (stages (n + 1)) := by\n"
    checks_root += "  interval_cases n\n"
    checks_root += "".join(f"  · exact {stage_name(step)}_valid\n" for step in range(1, len(stages)))
    checks_root += "end UdonVerify.SafeGcd.Cert255\n"
    write(output / "Divsteps255Checks.lean", "import Divsteps255Data\nimport Mathlib.Tactic.IntervalCases\n" + checks_root)
    return paths


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True, help="Existing Lean project directory")
    args = parser.parse_args()
    output = args.output.resolve()
    if not output.is_dir():
        raise RuntimeError("The Lean output directory must already exist")
    reserved = ["Divsteps255Data", "Divsteps255Checks", "Divsteps255Data.lean",
                "Divsteps255Checks.lean", "safegcd-certificate.json"]
    if any((output / name).exists() for name in reserved):
        raise RuntimeError("Refusing to overwrite certificate modules")
    started = time.monotonic()
    stages = generate_stages()
    paths = write_modules(output, stages)
    record = {
        "kind": "untrusted-generated-hulls",
        "bound": str(BOUND),
        "precision": PRECISION,
        "last_step": LAST_STEP,
        "nodes": sum(len(nodes) for nodes in stages),
        "vertices": sum(len(node.compact) for nodes in stages for node in nodes),
        "modules": {
            str(path.relative_to(output)): hashlib.sha256(path.read_bytes()).hexdigest()
            for path in paths
        },
    }
    (output / "safegcd-certificate.json").write_text(json.dumps(record, indent=2) + "\n")
    print(json.dumps({key: value for key, value in record.items() if key != "modules"}), flush=True)
    print(f"Generated untrusted modules in {time.monotonic() - started:.1f}s; Lean checking is required.",
          flush=True)


if __name__ == "__main__":
    main()
