"""Tests for wafan.solver_setup – lazy z3-noodler download."""

from pathlib import Path

import pytest

from wafan import solver_setup


class TestAssetNameFor:
    def test_linux_x86_64(self):
        assert solver_setup.asset_name_for(("Linux", "x86_64")) == (
            "z3-noodler-ubuntu-24.04-x86_64-shared"
        )

    def test_macos_arm64(self):
        assert solver_setup.asset_name_for(("Darwin", "arm64")) == (
            "z3-noodler-macos-15-arm64-shared"
        )

    def test_macos_intel(self):
        assert solver_setup.asset_name_for(("Darwin", "x86_64")) == (
            "z3-noodler-macos-15-intel-x86_64-shared"
        )

    def test_unsupported_platform_returns_none(self):
        assert solver_setup.asset_name_for(("Windows", "AMD64")) is None
        assert solver_setup.asset_name_for(("Linux", "aarch64")) is None


class TestCacheDir:
    def test_respects_override_env_var(self, monkeypatch, tmp_path):
        monkeypatch.setenv("WAFAN_CACHE_DIR", str(tmp_path))
        assert solver_setup.cache_dir() == tmp_path


class TestEnsureZ3Noodler:
    def test_unsupported_platform_returns_none(self, monkeypatch):
        monkeypatch.setattr(solver_setup, "asset_name_for", lambda *_: None)
        assert solver_setup.ensure_z3_noodler() is None

    def test_returns_cached_path_without_downloading(self, monkeypatch, tmp_path):
        monkeypatch.setenv("WAFAN_CACHE_DIR", str(tmp_path))
        version = "v1.6.1"
        asset = "z3-noodler-ubuntu-24.04-x86_64-shared"
        monkeypatch.setattr(solver_setup, "asset_name_for", lambda *_: asset)
        cached = tmp_path / version / asset
        cached.parent.mkdir(parents=True)
        cached.write_bytes(b"fake binary")

        def _boom(*_args, **_kwargs):
            raise AssertionError("should not attempt to download a cached binary")

        monkeypatch.setattr(solver_setup.urllib.request, "urlretrieve", _boom)
        result = solver_setup.ensure_z3_noodler(version=version, quiet=True)
        assert result == cached

    def test_download_failure_returns_none(self, monkeypatch, tmp_path):
        monkeypatch.setenv("WAFAN_CACHE_DIR", str(tmp_path))
        monkeypatch.setattr(
            solver_setup, "asset_name_for", lambda *_: "z3-noodler-ubuntu-24.04-x86_64-shared"
        )

        def _fail(*_args, **_kwargs):
            raise OSError("network unreachable")

        monkeypatch.setattr(solver_setup.urllib.request, "urlretrieve", _fail)
        result = solver_setup.ensure_z3_noodler(version="v1.6.1", quiet=True)
        assert result is None

    def test_download_success_caches_and_marks_executable(self, monkeypatch, tmp_path):
        monkeypatch.setenv("WAFAN_CACHE_DIR", str(tmp_path))
        asset = "z3-noodler-ubuntu-24.04-x86_64-shared"
        monkeypatch.setattr(solver_setup, "asset_name_for", lambda *_: asset)

        def _fake_download(_url, dest):
            Path(dest).write_bytes(b"fake binary")

        monkeypatch.setattr(solver_setup.urllib.request, "urlretrieve", _fake_download)
        result = solver_setup.ensure_z3_noodler(version="v1.6.1", quiet=True)
        assert result is not None
        assert result.is_file()
        assert result.stat().st_mode & 0o111
