#!/usr/bin/env python3
from pathlib import PurePosixPath

ROOT = PurePosixPath('/pkg')

def confined(rel: str) -> bool:
    parts = PurePosixPath(rel).parts
    return rel != '' and '..' not in parts and not PurePosixPath(rel).is_absolute()

def main() -> None:
    assert confined('src/main.rs')
    assert confined('lib/module.ts')
    assert not confined('../secret')
    assert not confined('/etc/passwd')
    assert not confined('a/../../b')
    print('package path confinement: traversal and absolute paths rejected')

if __name__ == '__main__': main()
