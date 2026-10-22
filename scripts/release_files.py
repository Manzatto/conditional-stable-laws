"""Select portable source files for the GitHub source archive."""

from pathlib import Path


OMITTED = {"ConditionedStableLaws/Cited/KellerLiverani.lean"}


def source_files(root):
    paths = [root / name for name in (
        ".gitignore", "README.md", "coverage.json", "lakefile.toml",
        "lake-manifest.json", "lean-toolchain")]
    paths.extend(root.glob("*.lean"))
    for directory, pattern in (("ConditionedStableLaws", "*.lean"),
                               ("docs", "*.md"), ("scripts", "*.py"),
                               (".github", "*.yml"), (".github", "*.yaml")):
        paths.extend((root / directory).rglob(pattern))
    selected = []
    for path in paths:
        if path.is_symlink():
            raise ValueError("Release sources must be ordinary files: " + str(path))
        if path.is_file() and path.relative_to(root).as_posix() not in OMITTED:
            selected.append(path)
    return sorted(set(selected), key=lambda path: path.relative_to(root).as_posix())
