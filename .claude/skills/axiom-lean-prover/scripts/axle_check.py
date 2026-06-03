#!/usr/bin/env python3
"""
axle_check.py — Verify Lean 4 proofs via the hosted Axiom AXLE API.

This is the ground-truth verifier for the `mathematics_axiom` domain. It REPLACES
a local `lake build`: there is no local Lean toolchain and no Mathlib cache. Each
`.lean` file is sent as text to https://axle.axiommath.ai/api/v1/check, where
Axiom's server checks it against a preloaded full Mathlib and returns structured
messages (errors / warnings / sorries) with source positions.

GROUND-TRUTH RULE (mirrors `lake build` exit 0 + `grep sorry`):
    PROVEN  <=>  okay == true  AND  no errors  AND  no `sorry` warning.

A `sorry`-stubbed proof returns okay==true with a `declaration uses 'sorry'`
WARNING — it *compiles* but is NOT proven. We treat that as INCOMPLETE, exactly
like the old domain grepped for `sorry` after a green build.

IMPORTS: the AXLE default environment expects exactly `import Mathlib`. This script
strips every `import ...` line from the submitted code, prepends a single
`import Mathlib`, and sets `ignore_imports: true`. So you may write any imports you
like (or local cross-file imports for multi-file proofs) — they are normalized
away and everything is checked against full Mathlib.

USAGE:
    python axle_check.py FILE.lean [FILE2.lean ...]   # check files (concatenated in given order)
    python axle_check.py --dir proofs/                # check every .lean under a dir
    python axle_check.py --code "theorem t : 1=1 := rfl"
    cat proof.lean | python axle_check.py -           # read from stdin
    python axle_check.py FILE.lean --statement-check   # accept `sorry` (for type-checking a stub)
    python axle_check.py FILE.lean --json              # also print the raw API response

ENV:
    AXLE_API_KEY   (required)  Bearer token, get one at https://axle.axiommath.ai
    AXLE_ENV       (optional)  Lean environment, default "lean-4.29.0"
    AXLE_API_URL   (optional)  Override the endpoint URL

EXIT CODES (so this slots into a build-like loop):
    0  COMPLETE          compiles, no errors, no sorry  -> proof is done
    2  INCOMPLETE_SORRY  compiles, but uses `sorry`      -> statement OK, proof unfinished
    1  ERROR             compile / type / tactic error   -> read messages and fix
    3  TRANSPORT_ERROR   network / auth / quota / usage error
"""
from __future__ import annotations

import argparse
import json
import os
import re
import sys
import urllib.error
import urllib.request
from pathlib import Path

DEFAULT_URL = os.environ.get("AXLE_API_URL", "https://axle.axiommath.ai/api/v1/check")
DEFAULT_ENV = os.environ.get("AXLE_ENV", "lean-4.29.0")

_IMPORT_RE = re.compile(r"^\s*import\b.*$")
_SORRY_RE = re.compile(r"uses\s+[`'\"]?sorry", re.IGNORECASE)
# Order multi-file proofs so definitions precede the lemmas/theorems that use them.
_ORDER_HINTS = ("definition", "notation", "basic", "lemma", "prop", "theorem", "main")

# Written on every run so error positions like `-:7:12` map to real lines you can open.
_LAST_CHECK = ".axle_last_check.lean"


def _normalize(code: str) -> str:
    """Drop all import lines and prepend a single `import Mathlib` (what AXLE expects)."""
    body = "\n".join(ln for ln in code.splitlines() if not _IMPORT_RE.match(ln))
    return "import Mathlib\n\n" + body.strip() + "\n"


def _order_lean(paths: list[Path]) -> list[Path]:
    def key(p: Path):
        name = p.stem.lower()
        for i, hint in enumerate(_ORDER_HINTS):
            if hint in name:
                return (i, name)
        return (len(_ORDER_HINTS), name)

    return sorted(paths, key=key)


def _gather_files(paths: list[str], scan_dir: str | None) -> list[Path]:
    files: list[Path] = []
    if scan_dir:
        files.extend(_order_lean(list(Path(scan_dir).rglob("*.lean"))))
    for p in paths:
        pp = Path(p)
        if pp.is_dir():
            files.extend(_order_lean(list(pp.rglob("*.lean"))))
        else:
            files.append(pp)
    return files


def _read_content(args) -> str:
    if args.code is not None:
        return args.code
    if args.files == ["-"]:
        return sys.stdin.read()
    files = _gather_files([f for f in args.files if f != "-"], args.dir)
    if not files:
        sys.stderr.write("error: no .lean input (pass files, --dir, --code, or '-')\n")
        sys.exit(3)
    chunks = []
    for f in files:
        if not f.is_file():
            sys.stderr.write(f"error: not a file: {f}\n")
            sys.exit(3)
        chunks.append(f"-- ===== {f} =====\n{f.read_text(encoding='utf-8')}")
    return "\n\n".join(chunks)


def _post(content: str, env: str, url: str, key: str, timeout: float) -> dict:
    payload = {
        "content": content,
        "environment": env,
        "ignore_imports": True,
        "timeout_seconds": timeout,
    }
    data = json.dumps(payload).encode("utf-8")
    req = urllib.request.Request(url, data=data, method="POST")
    req.add_header("Content-Type", "application/json; charset=utf-8")
    if key:
        req.add_header("Authorization", f"Bearer {key}")
    with urllib.request.urlopen(req, timeout=timeout + 30) as resp:
        return json.loads(resp.read().decode("utf-8"))


def main() -> int:
    ap = argparse.ArgumentParser(description="Verify Lean proofs via the Axiom AXLE API.")
    ap.add_argument("files", nargs="*", help="Lean files to check (concatenated in order), or '-' for stdin")
    ap.add_argument("--dir", help="Check every .lean file under this directory")
    ap.add_argument("--code", help="Check this inline Lean source string")
    ap.add_argument("--environment", default=DEFAULT_ENV, help=f"Lean environment (default {DEFAULT_ENV})")
    ap.add_argument("--timeout", type=float, default=120.0, help="Server-side check timeout in seconds")
    ap.add_argument("--statement-check", action="store_true",
                    help="Treat `sorry` as success (exit 0) — for confirming a stub type-checks")
    ap.add_argument("--json", action="store_true", help="Also print the raw JSON response")
    args = ap.parse_args()

    # Lean messages are full of Unicode (ℕ, ⊢, ↦, …). Force UTF-8 output so they
    # print on any locale (e.g. a GBK Windows console), not just the Linux container.
    for _stream in (sys.stdout, sys.stderr):
        try:
            _stream.reconfigure(encoding="utf-8", errors="replace")
        except (AttributeError, ValueError):
            pass

    key = os.environ.get("AXLE_API_KEY", "")
    if not key:
        sys.stderr.write(
            "error: AXLE_API_KEY is not set. Add it to .env "
            "(get a key at https://axle.axiommath.ai).\n"
        )
        return 3

    raw_content = _read_content(args)
    content = _normalize(raw_content)
    Path(_LAST_CHECK).write_text(content, encoding="utf-8")

    try:
        resp = _post(content, args.environment, DEFAULT_URL, key, args.timeout)
    except urllib.error.HTTPError as e:
        body = e.read().decode("utf-8", "replace")
        sys.stderr.write(f"TRANSPORT_ERROR: HTTP {e.code} from AXLE\n{body}\n")
        return 3
    except urllib.error.URLError as e:
        sys.stderr.write(f"TRANSPORT_ERROR: cannot reach AXLE ({e.reason})\n")
        return 3

    if args.json:
        print(json.dumps(resp, indent=2, ensure_ascii=False))

    # A usage error (bad request, quota, env) — not a Lean error.
    if "user_error" in resp:
        sys.stderr.write(f"TRANSPORT_ERROR: {resp['user_error']}\n")
        return 3

    lean = resp.get("lean_messages", {}) or {}
    errors = lean.get("errors", []) or []
    warnings = lean.get("warnings", []) or []
    okay = bool(resp.get("okay", False))
    failed = resp.get("failed_declarations", []) or []
    sorries = [w for w in warnings if _SORRY_RE.search(w)]
    other_warnings = [w for w in warnings if not _SORRY_RE.search(w)]

    if not okay or errors:
        status, code = "ERROR", 1
    elif sorries:
        status, code = "INCOMPLETE_SORRY", (0 if args.statement_check else 2)
    else:
        status, code = "COMPLETE", 0

    timings = resp.get("info", {}) or {}
    ms = timings.get("total_request_time_ms", resp.get("timings", {}).get("total_ms", "?"))

    print(f"AXLE [{args.environment}]  STATUS: {status}   ({ms} ms)")
    print(f"  errors: {len(errors)}   sorries: {len(sorries)}   "
          f"warnings: {len(other_warnings)}   failed_decls: {failed or '[]'}")

    for e in errors:
        print("\n--- error ---")
        print(e.rstrip())
    for w in sorries:
        print("\n--- sorry ---")
        print(w.rstrip())
    for w in other_warnings:
        print("\n--- warning ---")
        print(w.rstrip())

    if status == "COMPLETE":
        print("\n✓ Formally verified: compiles against Mathlib, no errors, no sorry.")
    elif status == "INCOMPLETE_SORRY":
        print(f"\n⚠ Type-checks but uses `sorry` — NOT a proof. "
              f"Replace every sorry. (Positions are relative to {_LAST_CHECK}.)")
    else:
        print(f"\n✗ Does not verify. Fix the errors above. "
              f"(Positions like `-:L:C` are relative to {_LAST_CHECK}.)")

    return code


if __name__ == "__main__":
    sys.exit(main())
