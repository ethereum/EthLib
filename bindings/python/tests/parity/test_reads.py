"""The archive paths that the runner of each execution format reads, without the archives."""

import pytest

from .catalogue import FORMATS, Case
from .runners import reads

PATH = "fixtures/blockchain_tests_engine_x/for_prague/prague/eip7702/cases.json"


def test_engine_x_reads_the_shared_states_of_its_format():
    case = Case("execution-spec-tests", "", "Prague", "blockchain_test_engine_x", "id", PATH)
    assert reads(case) == [PATH, "fixtures/blockchain_tests_engine_x/pre_alloc"]


@pytest.mark.parametrize("group", [g for g in FORMATS if g != "blockchain_test_engine_x"])
def test_other_formats_read_their_file_alone(group: str):
    path = f"fixtures/{group}s/for_prague/prague/eip7702/cases.json"
    assert reads(Case("execution-spec-tests", "", "Prague", group, "id", path)) == [path]
