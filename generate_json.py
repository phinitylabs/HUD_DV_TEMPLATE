#!/usr/bin/env python3
"""Generate local-hud.json file for the axi4_slave_sva problem."""

import os
import sys
import json

# Ensure MCP tools do not load during import
os.environ["MCP_TESTING_MODE"] = "0"

sys.path.insert(0, '.')

from utils.imagectl3 import ProcessedSpec, hud_dict, generate_jsons
import hud_controller.problems
from hud_controller.utils import import_submodules
from hud_controller.spec import PROBLEM_REGISTRY

# Import all extractors so their @problem decorators register specs
import_submodules(hud_controller.problems)

# Filter for our problem
problem_specs = [s for s in PROBLEM_REGISTRY if s.id == 'axi4_slave_sva']

if not problem_specs:
    print("ERROR: Problem 'axi4_slave_sva' not found in PROBLEM_REGISTRY")
    print(f"Available problems: {[s.id for s in PROBLEM_REGISTRY]}")
    sys.exit(1)

print(f"Found {len(problem_specs)} problem(s)")

# Create ProcessedSpec for each problem
# ProcessedSpec needs: id, description, image, base, test, golden, hints
specs = []
for spec in problem_specs:
    # Get the base name from args (we'll use 'verilog_' as default)
    image_base = 'verilog_'
    processed = ProcessedSpec(
        id=spec.id,
        description=spec.description,
        image=image_base + spec.id,
        base=spec.base,
        test=spec.test,
        golden=spec.golden,
        hints="none"
    )
    specs.append(processed)

# Generate JSON files
generate_jsons(specs)

print("✅ Generated JSON files:")
print("  - local-claude-hud.json")
print("  - local-openai-hud.json")
print("  - remote-claude-hud.json")
print("  - remote-openai-hud.json")
print("\nTo use with Claude agent, use: local-claude-hud.json")

