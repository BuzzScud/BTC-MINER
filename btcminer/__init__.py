"""BTC Miner for macOS, Linux, and Windows. GPL-3.0."""
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parent.parent
LEGACY = Path(__file__).resolve().parent / "legacy"
if str(LEGACY) not in sys.path:
    sys.path.insert(0, str(LEGACY))
VERSION = "1.5.0"
