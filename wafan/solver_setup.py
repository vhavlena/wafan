"""Lazy download of a prebuilt z3-noodler binary for the current platform.

z3-noodler (https://github.com/VeriFIT/z3-noodler) does not ship on PyPI, so
users would otherwise have to build or install it themselves. This module
downloads the matching release asset on first use and caches it locally, so
`wafan` works out of the box on the platforms z3-noodler publishes binaries
for (Linux x86_64, macOS arm64/x86_64).
"""

from __future__ import annotations

import os
import platform
import stat
import sys
import urllib.request
from pathlib import Path

#: Pinned release; override with WAFAN_Z3_NOODLER_VERSION to track another tag.
_DEFAULT_VERSION = "v1.6.1"

_REPO = "VeriFIT/z3-noodler"

#: (system, machine) -> release asset name, per https://github.com/VeriFIT/z3-noodler/releases
_ASSETS = {
    ("Linux", "x86_64"): "z3-noodler-ubuntu-24.04-x86_64-shared",
    ("Darwin", "arm64"): "z3-noodler-macos-15-arm64-shared",
    ("Darwin", "x86_64"): "z3-noodler-macos-15-intel-x86_64-shared",
}


def current_platform_key() -> tuple[str, str]:
    return (platform.system(), platform.machine())


def asset_name_for(platform_key: tuple[str, str] | None = None) -> str | None:
    """Return the release asset name for a (system, machine) pair, or None if unsupported."""
    return _ASSETS.get(platform_key or current_platform_key())


def cache_dir() -> Path:
    """Directory where downloaded solver binaries are cached."""
    override = os.environ.get("WAFAN_CACHE_DIR")
    if override:
        return Path(override)
    if sys.platform == "darwin":
        base = Path.home() / "Library" / "Caches"
    elif os.name == "nt":
        base = Path(os.environ.get("LOCALAPPDATA", Path.home()))
    else:
        base = Path(os.environ.get("XDG_CACHE_HOME", Path.home() / ".cache"))
    return base / "wafan" / "solvers"


def ensure_z3_noodler(version: str | None = None, quiet: bool = False) -> Path | None:
    """Return a local path to a working z3-noodler binary, downloading it if needed.

    Returns None if the current platform has no published binary or the
    download fails; callers should fall back to a system-installed solver.
    """
    asset = asset_name_for()
    if asset is None:
        return None

    version = version or os.environ.get("WAFAN_Z3_NOODLER_VERSION", _DEFAULT_VERSION)
    dest_dir = cache_dir() / version
    dest = dest_dir / asset
    if dest.is_file():
        return dest

    url = f"https://github.com/{_REPO}/releases/download/{version}/{asset}"
    if not quiet:
        print(f"wafan: downloading z3-noodler {version} ({asset})...", file=sys.stderr)

    dest_dir.mkdir(parents=True, exist_ok=True)
    tmp = dest.with_suffix(".part")
    try:
        urllib.request.urlretrieve(url, tmp)
    except OSError as exc:
        if not quiet:
            print(f"wafan: failed to download z3-noodler: {exc}", file=sys.stderr)
        tmp.unlink(missing_ok=True)
        return None

    tmp.chmod(tmp.stat().st_mode | stat.S_IXUSR | stat.S_IXGRP | stat.S_IXOTH)
    tmp.rename(dest)
    return dest


def download_solver_cli(argv: list[str] | None = None) -> int:
    """Entry point for the `wafan-download-solver` console script.

    Pre-fetches the z3-noodler binary so it's already cached before the
    first `wafan` run — useful in CI/Docker image builds or offline setups.
    """
    import argparse

    parser = argparse.ArgumentParser(
        prog="wafan-download-solver",
        description="Pre-fetch the z3-noodler binary used by wafan, without running an analysis.",
    )
    parser.add_argument(
        "--version",
        default=None,
        metavar="TAG",
        help=f"z3-noodler release tag to download (default: {_DEFAULT_VERSION}, or $WAFAN_Z3_NOODLER_VERSION).",
    )
    args = parser.parse_args(argv)

    path = ensure_z3_noodler(version=args.version)
    if path is None:
        print(
            "wafan: no prebuilt z3-noodler binary available for this platform "
            f"({current_platform_key()}); falling back to 'z3' on PATH at runtime",
            file=sys.stderr,
        )
        return 1
    print(f"wafan: z3-noodler ready at {path}")
    return 0
