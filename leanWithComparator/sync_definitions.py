"""Copy the model definitions from the FC statement into the solution module."""

from argparse import ArgumentParser
from pathlib import Path

HERE = Path(__file__).resolve().parent
CHALLENGE = HERE.parent / "FClikelean" / "104variant.lean"
DEFINITIONS = HERE / "Definitions.lean"
BOUNDARY = "\n-- The challenge theorem follows.\n"
FC_ATTRIBUTES = "public meta import FormalConjecturesUtil.Attributes.Basic\n"


def main():
    parser = ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true", help="check the generated file")
    args = parser.parse_args()

    source = CHALLENGE.read_text(encoding="utf-8")
    prefix, separator, _ = source.partition(BOUNDARY)
    if not separator or source.count(BOUNDARY) != 1 or prefix.count(FC_ATTRIBUTES) != 1:
        parser.error("unexpected definitions boundary or FC import in FClikelean/104variant.lean")

    expected = (
        "-- Generated from FClikelean/104variant.lean by sync_definitions.py.\n"
        + prefix.replace(FC_ATTRIBUTES, "").rstrip()
        + "\n\nend Erdos104\n"
    )
    if args.check:
        if not DEFINITIONS.is_file() or DEFINITIONS.read_text(encoding="utf-8") != expected:
            parser.exit(
                1, "Definitions.lean is stale. Run python3 leanWithComparator/sync_definitions.py.\n"
            )
    else:
        DEFINITIONS.write_text(expected, encoding="utf-8")


if __name__ == "__main__":
    main()
