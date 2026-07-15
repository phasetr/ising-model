#!/usr/bin/env python3
"""Independent external-review authority for revision-18 setup evidence."""

from __future__ import annotations

import argparse
from pathlib import Path

import manager


def main() -> None:
    """Create the sole external setup-review artifact; never run calibration."""

    parser = argparse.ArgumentParser()
    parser.add_argument("operation", choices=["create"])
    parser.add_argument("--authority", required=True)
    args = parser.parse_args()
    package = Path(__file__).resolve().parent
    protocol = manager.verify_package(package)
    manager.create_review(protocol, Path(protocol["execution_root"]), Path(protocol["review_root"]),
                          args.authority)


if __name__ == "__main__":
    main()
