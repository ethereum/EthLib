"""The execution forks on which the precompile suites run, in order."""

FORKS = (
    "frontier", "homestead", "daoFork", "tangerineWhistle", "spuriousDragon", "byzantium",
    "constantinople", "petersburg", "istanbul", "muirGlacier", "berlin", "london",
    "arrowGlacier", "grayGlacier", "paris", "shapella", "dencun", "pectra", "fusaka", "bpo1",
    "bpo2", "bpo3", "bpo4", "bpo5",
)


def since(first: str, before: str | None = None) -> tuple[str, ...]:
    """The forks from `first`, up to the fork before `before` when it is given."""
    end = FORKS.index(before) if before else len(FORKS)
    return FORKS[FORKS.index(first):end]


def ends(first: str) -> tuple[str, ...]:
    """The fork `first` and the latest fork, for a precompile that no later fork changes."""
    return tuple(dict.fromkeys((first, FORKS[-1])))
