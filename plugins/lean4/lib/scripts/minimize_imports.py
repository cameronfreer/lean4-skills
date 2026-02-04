#!/usr/bin/env python3
"""
minimize_imports.py - Remove unused imports from Lean 4 files

Usage:
    ./minimize_imports.py <file> [--dry-run] [--verbose]

This script identifies and removes unused imports by:
1. Extracting all imports from the file
2. Temporarily removing each import one at a time
3. Checking if the file still compiles
4. Removing imports that don't cause compilation errors

Modes:
    --dry-run: Show what would be removed without modifying file
    --verbose: Show detailed compilation output

Examples:
    ./minimize_imports.py MyFile.lean
    ./minimize_imports.py src/Main.lean --dry-run
    ./minimize_imports.py Core.lean --verbose

Notes:
    - Requires lake build to be working
    - Creates temporary backup (.minimize_backup)
    - Safe: Restores original on errors
    - May take several minutes for files with many imports
"""

import re
import sys
import subprocess
import shutil
from pathlib import Path
from typing import List, Tuple, Set

def extract_imports(content: str) -> List[Tuple[int, str]]:
    """Extract all import statements with their line numbers (1-indexed)"""
    imports = []
    lines = content.split('\n')
    for i, line in enumerate(lines):
        # Match import statements (handling various formats)
        match = re.match(r'^import\s+(.+?)(?:\s*--.*)?$', line.strip())
        if match:
            imports.append((i + 1, line))  # 1-indexed
    return imports

def remove_import_line(content: str, line_num: int) -> str:
    """Remove the import at the given line number (1-indexed)"""
    lines = content.split('\n')
    if 0 < line_num <= len(lines):
        lines[line_num - 1] = ''  # Remove the line
    return '\n'.join(lines)

def check_compiles(filepath: Path, verbose: bool = False) -> Tuple[bool, str]:
    """Check if the file compiles using lake env lean"""
    try:
        result = subprocess.run(
            ['lake', 'env', 'lean', str(filepath)],
            capture_output=True,
            text=True,
            timeout=60  # 60 second timeout per check
        )

        output = result.stdout + result.stderr

        if verbose:
            print(f"    Compilation output:\n{output[:500]}")

        # Check for errors (but not warnings)
        # Lean compilation succeeds with exit code 0 even with warnings
        success = result.returncode == 0

        return success, output
    except subprocess.TimeoutExpired:
        return False, "Compilation timed out"
    except Exception as e:
        return False, f"Error running lean: {e}"

def minimize_imports(filepath: Path, dry_run: bool = False, verbose: bool = False) -> None:
    """Minimize imports in the given Lean file"""

    if not filepath.exists():
        print(f"Error: File {filepath} does not exist", file=sys.stderr)
        sys.exit(1)

    print(f"Analyzing imports in {filepath}")

    # Read original content
    with open(filepath, 'r', encoding='utf-8') as f:
        original_content = f.read()

    # Extract imports
    imports = extract_imports(original_content)

    if not imports:
        print("No imports found in file")
        return

    print(f"Found {len(imports)} import(s)")

    # Create backup
    backup_path = filepath.with_suffix(filepath.suffix + '.minimize_backup')
    if not dry_run:
        shutil.copy2(filepath, backup_path)
        print(f"Created backup: {backup_path}")

    # Check original file compiles
    print("\nChecking original file compiles...")
    compiles, output = check_compiles(filepath, verbose)

    if not compiles:
        print(f"ERROR: Original file doesn't compile!", file=sys.stderr)
        print(f"Cannot minimize imports for a file with compilation errors", file=sys.stderr)
        if verbose:
            print(f"\nCompilation output:\n{output}")
        sys.exit(1)

    print("✓ Original file compiles successfully")

    # Try removing each import
    unused_imports = []
    used_imports = []

    print(f"\nTesting each import (this may take a while)...")

    for i, (line_num, import_line) in enumerate(imports, 1):
        import_name = import_line.strip()
        print(f"  [{i}/{len(imports)}] Testing: {import_name}")

        # Create version without this import
        modified_content = remove_import_line(original_content, line_num)

        # Write temporarily
        if not dry_run:
            with open(filepath, 'w', encoding='utf-8') as f:
                f.write(modified_content)

        # Check if it still compiles
        if not dry_run:
            compiles, _ = check_compiles(filepath, verbose=False)
        else:
            # In dry-run, simulate by checking if import is obviously used
            # This is a heuristic and not perfect
            import_module = import_name.replace('import', '').strip()
            module_base = import_module.split('.')[-1]

            # Simple heuristic: check if module name appears in file
            compiles = module_base not in original_content

        if compiles:
            unused_imports.append(import_line)
            print(f"    → Appears UNUSED ✗")
        else:
            used_imports.append(import_line)
            print(f"    → Required ✓")

        # Restore original
        if not dry_run:
            with open(filepath, 'w', encoding='utf-8') as f:
                f.write(original_content)

    # Report results
    print("\n" + "=" * 80)
    print("RESULTS")
    print("=" * 80)

    print(f"\nUsed imports: {len(used_imports)}")
    for imp in used_imports:
        print(f"  ✓ {imp.strip()}")

    if unused_imports:
        print(f"\nUnused imports: {len(unused_imports)}")
        for imp in unused_imports:
            print(f"  ✗ {imp.strip()}")

        if dry_run:
            print("\n[DRY RUN] Would remove the unused imports above")
            print(f"Run without --dry-run to actually remove them")
        else:
            print("\nRemoving unused imports...")

            # Build set of lines to remove
            lines_to_remove = set()
            for line_num, import_line in imports:
                if import_line in unused_imports:
                    lines_to_remove.add(line_num)

            # Remove unused imports
            lines = original_content.split('\n')
            for line_num in sorted(lines_to_remove, reverse=True):
                if 0 < line_num <= len(lines):
                    lines[line_num - 1] = ''

            # Remove consecutive blank lines in import region
            cleaned_lines = []
            prev_blank = False
            for i, line in enumerate(lines):
                is_blank = line.strip() == ''
                # Keep non-blank lines and first blank after content
                if not is_blank or not prev_blank or i >= 50:  # Only compress blanks in import region
                    cleaned_lines.append(line)
                prev_blank = is_blank

            minimized_content = '\n'.join(cleaned_lines)

            # Write minimized version
            with open(filepath, 'w', encoding='utf-8') as f:
                f.write(minimized_content)

            # Verify it still compiles
            print("\nVerifying minimized file compiles...")
            compiles, output = check_compiles(filepath, verbose)

            if compiles:
                print("✓ Minimized file compiles successfully!")
                print(f"\nRemoved {len(unused_imports)} unused import(s)")
                print(f"Backup saved to: {backup_path}")
            else:
                print("ERROR: Minimized file doesn't compile!", file=sys.stderr)
                print("Restoring original file...", file=sys.stderr)
                shutil.copy2(backup_path, filepath)
                print("Original file restored", file=sys.stderr)
                if verbose:
                    print(f"\nCompilation output:\n{output}")
                sys.exit(1)
    else:
        print("\n✓ All imports are used!")
        if not dry_run:
            # Remove backup since no changes were made
            backup_path.unlink()

def main():
    if len(sys.argv) < 2:
        print(__doc__)
        sys.exit(1)

    filepath = Path(sys.argv[1])
    dry_run = '--dry-run' in sys.argv
    verbose = '--verbose' in sys.argv

    if dry_run:
        print("[DRY RUN MODE] - No files will be modified\n")

    minimize_imports(filepath, dry_run, verbose)

if __name__ == '__main__':
    main()
