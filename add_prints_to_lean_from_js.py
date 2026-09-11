import os
import re
from pathlib import Path

def convert_exported_item(item: str) -> str:
    item = item.strip()
    # Handle names like $Expr$add -> Expr
    if item.startswith('$'):
        parts = [p for p in item.split('$') if p]
        return parts[0] if parts else item
    return item

def process_file(js_path: Path):
    with open(js_path, "r", encoding="utf-8") as f:
        lines = [line.strip() for line in f if line.strip()]

    if not lines:
        return

    # Extract the exported items from the last line
    last_line = lines[-1]
    match = re.search(r'export\s*\{([^}]+)\};?', last_line)
    if not match:
        return

    raw_exports = match.group(1).split(',')

    # Map and deduplicate preserving order
    lean_targets = []
    seen = set()
    for raw in raw_exports:
        target = convert_exported_item(raw)
        if target and target not in seen:
            seen.add(target)
            lean_targets.append(target)

    if not lean_targets:
        return

    # Find the corresponding .lean file
    lean_candidates = [
        Path("LeanJsCliSnapshots") / f"{js_path.stem}.lean",
        js_path.with_suffix(".lean"),
    ]

    lean_path = next((p for p in lean_candidates if p.exists()), None)

    # Fallback: search anywhere in the current directory tree
    if not lean_path:
        found = list(Path('.').glob(f"**/{js_path.stem}.lean"))
        if found:
            lean_path = found[0]

    if not lean_path:
        print(f"[-] No matching Lean file found for {js_path.name}")
        return

    # Construct the comment line
    comment_line = f"-- @js_export: {', '.join(lean_targets)}\n"

    with open(lean_path, "r", encoding="utf-8") as f:
        content = f.read()

    # If the file already begins with a @js_export comment, replace it
    if content.startswith("-- @js_export:"):
        first_newline = content.find("\n")
        rest = content[first_newline + 1:] if first_newline != -1 else ""
        new_content = comment_line + rest
    else:
        new_content = comment_line + content

    if new_content != content:
        with open(lean_path, "w", encoding="utf-8") as f:
            f.write(new_content)
        print(f"[+] Updated {lean_path} -> {comment_line.strip()}")
    else:
        print(f"[=] {lean_path} is already up to date")

def main():
    for js_file in Path('.').glob('**/*.js'):
        if any(part.startswith('.') or part in ('node_modules', 'dist') for part in js_file.parts):
            continue
        process_file(js_file)

if __name__ == "__main__":
    main()
