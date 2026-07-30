#!/usr/bin/env python3
"""Extract the Treiber source descriptor at an explicit trust boundary.

This is a deliberately narrow Clang-AST checker for c/treiber.c.  It is not a
proved C semantics frontend and must not be cited as one.  Its output records
the source facts that the Lean development may later import through an
explicitly trusted translation boundary.
"""

from __future__ import annotations

import argparse
import difflib
import hashlib
import json
import re
import subprocess
import sys
from pathlib import Path
from typing import Any, Iterable


SCHEMA = "treiber-source-extraction-trust-boundary/v1"
EXPECTED_CLANG_MAJOR = 18
DEFAULT_DESCRIPTOR = "c/treiber.source-extraction-trust-boundary.json"
DEFAULT_LEAN_OUTPUT = "WeakMemory/TreiberExtractedProgram.lean"
AST_ARGS = (
    "-std=c11",
    "-Wall",
    "-Wextra",
    "-Werror",
    "-pedantic-errors",
    "-fsyntax-only",
    "-Xclang",
    "-ast-dump=json",
    "c/treiber.c",
)

AstNode = dict[str, Any]


class ExtractionError(RuntimeError):
    """The input did not have the exact source shape modeled here."""


def require(condition: bool, message: str) -> None:
    if not condition:
        raise ExtractionError(message)


def children(node: AstNode) -> list[AstNode]:
    return node.get("inner", [])


def walk(node: AstNode) -> Iterable[AstNode]:
    yield node
    for child in children(node):
        yield from walk(child)


def kind(node: AstNode) -> str:
    return node.get("kind", "")


def expect_kind(node: AstNode, expected: str, context: str) -> AstNode:
    require(
        kind(node) == expected,
        f"{context}: expected {expected}, found {kind(node) or '<missing>'}",
    )
    return node


def expect_child_kinds(
    node: AstNode, expected: tuple[str, ...], context: str
) -> list[AstNode]:
    actual_children = children(node)
    actual = tuple(kind(child) for child in actual_children)
    require(
        actual == expected,
        f"{context}: expected children {expected}, found {actual}",
    )
    return actual_children


def strip_expression(node: AstNode) -> AstNode:
    wrappers = {"ImplicitCastExpr", "ParenExpr", "CStyleCastExpr"}
    while kind(node) in wrappers:
        inner = children(node)
        require(
            len(inner) == 1,
            f"{kind(node)}: expected one wrapped expression, found {len(inner)}",
        )
        node = inner[0]
    return node


def referenced_name(node: AstNode, context: str) -> str:
    node = strip_expression(node)
    expect_kind(node, "DeclRefExpr", context)
    referenced = node.get("referencedDecl", {})
    name = referenced.get("name")
    require(isinstance(name, str), f"{context}: missing referenced declaration")
    return name


def enum_name(node: AstNode, context: str) -> str:
    node = strip_expression(node)
    expect_kind(node, "DeclRefExpr", context)
    referenced = node.get("referencedDecl", {})
    require(
        referenced.get("kind") == "EnumConstantDecl",
        f"{context}: expected an enum constant",
    )
    name = referenced.get("name")
    require(
        isinstance(name, str) and name.startswith("memory_order_"),
        f"{context}: expected a memory_order_* constant, found {name!r}",
    )
    return name.removeprefix("memory_order_")


def member_path(node: AstNode, context: str) -> str:
    node = strip_expression(node)
    expect_kind(node, "MemberExpr", context)
    require(node.get("isArrow") is True, f"{context}: expected pointer member access")
    member = node.get("name")
    require(isinstance(member, str), f"{context}: missing member name")
    inner = children(node)
    require(len(inner) == 1, f"{context}: malformed member base")
    base = referenced_name(inner[0], f"{context} base")
    return f"{base}->{member}"


def addressed_member(node: AstNode, context: str) -> str:
    expect_kind(node, "UnaryOperator", context)
    require(node.get("opcode") == "&", f"{context}: expected address-of")
    inner = children(node)
    require(len(inner) == 1, f"{context}: malformed address-of")
    return member_path(inner[0], context)


def addressed_variable(node: AstNode, context: str) -> str:
    expect_kind(node, "UnaryOperator", context)
    require(node.get("opcode") == "&", f"{context}: expected address-of")
    inner = children(node)
    require(len(inner) == 1, f"{context}: malformed address-of")
    return referenced_name(inner[0], context)


def is_null_pointer(node: AstNode) -> bool:
    saw_null_cast = any(
        candidate.get("castKind") == "NullToPointer"
        for candidate in walk(node)
    )
    saw_zero = any(
        kind(candidate) == "IntegerLiteral" and candidate.get("value") == "0"
        for candidate in walk(node)
    )
    return saw_null_cast and saw_zero


def expect_null_pointer(node: AstNode, context: str) -> None:
    require(is_null_pointer(node), f"{context}: expected the null pointer constant")


def source_location(node: AstNode) -> dict[str, int]:
    begin = node.get("range", {}).get("begin", {})
    location = begin.get("expansionLoc", begin)
    offset = location.get("offset")
    require(isinstance(offset, int), f"{kind(node)}: missing source byte offset")
    source = (
        Path(__file__).resolve().parents[1] / "c/treiber.c"
    ).read_bytes()
    require(0 <= offset < len(source), f"{kind(node)}: invalid source byte offset")
    line = source.count(b"\n", 0, offset) + 1
    previous_newline = source.rfind(b"\n", 0, offset)
    column = offset - previous_newline
    reported_column = location.get("col")
    require(
        reported_column is None or reported_column == column,
        f"{kind(node)}: Clang column disagrees with source byte offset",
    )
    return {"column": column, "line": line, "offset": offset}


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as source:
        for block in iter(lambda: source.read(1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest()


def function_body(function: AstNode) -> AstNode:
    bodies = [child for child in children(function) if kind(child) == "CompoundStmt"]
    require(
        len(bodies) == 1,
        f"{function.get('name')}: expected exactly one function body",
    )
    return bodies[0]


def function_parameters(function: AstNode) -> list[dict[str, str]]:
    return [
        {
            "name": parameter["name"],
            "type": parameter["type"]["qualType"],
        }
        for parameter in children(function)
        if kind(parameter) == "ParmVarDecl"
    ]


def variable_declaration(
    statement: AstNode, expected_name: str, context: str
) -> tuple[AstNode, AstNode]:
    expect_kind(statement, "DeclStmt", context)
    declaration_children = children(statement)
    require(
        len(declaration_children) == 1,
        f"{context}: expected one variable declaration",
    )
    declaration = expect_kind(declaration_children[0], "VarDecl", context)
    require(
        declaration.get("name") == expected_name,
        f"{context}: expected variable {expected_name!r}",
    )
    initializers = children(declaration)
    require(len(initializers) == 1, f"{context}: expected one initializer")
    return declaration, initializers[0]


def parse_atomic_load(
    node: AstNode,
    *,
    expected_order: str,
    result: str,
    context: str,
) -> dict[str, Any]:
    expect_kind(node, "AtomicExpr", context)
    require(
        node.get("name") == "__c11_atomic_load",
        f"{context}: expected __c11_atomic_load",
    )
    atomic_children = children(node)
    require(len(atomic_children) == 2, f"{context}: malformed atomic load")
    object_path = addressed_member(atomic_children[0], f"{context} object")
    order = enum_name(atomic_children[1], f"{context} memory order")
    require(
        order == expected_order,
        f"{context}: expected {expected_order}, found {order}",
    )
    require(
        object_path == "stack->head",
        f"{context}: expected stack->head, found {object_path}",
    )
    return {
        "kind": "atomic_load",
        "memory_order": order,
        "object": object_path,
        "result": result,
        "source": source_location(node),
    }


def parse_weak_compare_exchange(
    node: AstNode,
    *,
    expected_desired: str,
    expected_success_order: str,
    expected_failure_order: str,
    context: str,
) -> dict[str, Any]:
    expect_kind(node, "AtomicExpr", context)
    require(
        node.get("name") == "__c11_atomic_compare_exchange_weak",
        f"{context}: expected weak C11 compare-exchange",
    )
    atomic_children = children(node)
    require(
        len(atomic_children) == 5,
        f"{context}: malformed Clang 18 compare-exchange AST",
    )

    # Clang 18's AtomicExpr JSON order is:
    # object, success order, expected address, failure order, desired value.
    object_path = addressed_member(atomic_children[0], f"{context} object")
    success_order = enum_name(
        atomic_children[1], f"{context} success memory order"
    )
    expected = addressed_variable(
        atomic_children[2], f"{context} expected operand"
    )
    failure_order = enum_name(
        atomic_children[3], f"{context} failure memory order"
    )
    desired = referenced_name(atomic_children[4], f"{context} desired operand")

    require(
        object_path == "stack->head",
        f"{context}: expected stack->head, found {object_path}",
    )
    require(expected == "observed", f"{context}: expected &observed")
    require(
        desired == expected_desired,
        f"{context}: expected desired value {expected_desired}, found {desired}",
    )
    require(
        success_order == expected_success_order,
        f"{context}: expected success order {expected_success_order}, "
        f"found {success_order}",
    )
    require(
        failure_order == expected_failure_order,
        f"{context}: expected failure order {expected_failure_order}, "
        f"found {failure_order}",
    )

    return {
        "desired": desired,
        "expected": {
            "expression": f"&{expected}",
            "failure_update": {
                "semantic_basis": (
                    "C11 compare-exchange writes the current atomic-object "
                    "value through the expected operand on failure"
                ),
                "target": expected,
                "value": object_path,
            },
        },
        "failure_memory_order": failure_order,
        "kind": "atomic_compare_exchange",
        "object": object_path,
        "source": source_location(node),
        "strength": "weak",
        "success_memory_order": success_order,
    }


def parse_initialization(function: AstNode) -> dict[str, Any]:
    body_children = expect_child_kinds(
        function_body(function), ("AtomicExpr",), "treiber_init body"
    )
    atomic = body_children[0]
    require(
        atomic.get("name") == "__c11_atomic_init",
        "treiber_init: expected atomic_init",
    )
    atomic_children = children(atomic)
    require(len(atomic_children) == 2, "treiber_init: malformed atomic_init")
    object_path = addressed_member(atomic_children[0], "treiber_init object")
    expect_null_pointer(atomic_children[1], "treiber_init value")
    require(object_path == "stack->head", "treiber_init: unexpected object")
    return {
        "event": {
            "kind": "atomic_init",
            "object": object_path,
            "source": source_location(atomic),
            "value": "null",
        },
        "function": "treiber_init",
        "parameters": function_parameters(function),
        "signature": function["type"]["qualType"],
    }


def parse_push(function: AstNode) -> dict[str, Any]:
    body_children = expect_child_kinds(
        function_body(function), ("DeclStmt", "DoStmt"), "treiber_push body"
    )
    _, observed_initializer = variable_declaration(
        body_children[0], "observed", "treiber_push observed"
    )
    load = parse_atomic_load(
        observed_initializer,
        expected_order="relaxed",
        result="observed",
        context="treiber_push initial load",
    )

    loop = body_children[1]
    loop_children = expect_child_kinds(
        loop, ("CompoundStmt", "UnaryOperator"), "treiber_push do-while"
    )
    loop_body_children = expect_child_kinds(
        loop_children[0], ("BinaryOperator",), "treiber_push loop body"
    )
    assignment = loop_body_children[0]
    require(
        assignment.get("opcode") == "=",
        "treiber_push loop body: expected node->next assignment",
    )
    assignment_children = children(assignment)
    require(len(assignment_children) == 2, "treiber_push: malformed assignment")
    next_object = member_path(assignment_children[0], "treiber_push next write")
    next_value = referenced_name(
        assignment_children[1], "treiber_push next value"
    )
    require(next_object == "node->next", "treiber_push: unexpected field write")
    require(next_value == "observed", "treiber_push: unexpected next value")
    next_write = {
        "execution": "once_per_loop_attempt",
        "kind": "non_atomic_write",
        "object": next_object,
        "sequenced_before": "head_compare_exchange",
        "source": source_location(assignment),
        "value": next_value,
    }

    guard = loop_children[1]
    require(
        guard.get("opcode") == "!",
        "treiber_push: do-while guard must negate compare-exchange",
    )
    guard_children = children(guard)
    require(len(guard_children) == 1, "treiber_push: malformed loop guard")
    compare_exchange = parse_weak_compare_exchange(
        guard_children[0],
        expected_desired="node",
        expected_success_order="release",
        expected_failure_order="relaxed",
        context="treiber_push compare-exchange",
    )
    compare_exchange["loop_role"] = "negated_guard_retry_on_failure"

    return_statements = [
        node for node in walk(function_body(function)) if kind(node) == "ReturnStmt"
    ]
    require(not return_statements, "treiber_push: unexpected explicit return")

    return {
        "control_flow": {
            "loop": {
                "body_reexecuted_after_failure": True,
                "kind": "do_while",
                "retries_on": [
                    "weak_spurious_failure",
                    "head_value_mismatch",
                ],
                "terminates_on": "head_compare_exchange_success",
            },
            "return": {
                "after": "head_compare_exchange_success",
                "kind": "implicit_void",
            },
        },
        "events": [
            {"id": "head_load", **load},
            {"id": "next_write", **next_write},
            {"id": "head_compare_exchange", **compare_exchange},
        ],
        "name": "treiber_push",
        "parameters": function_parameters(function),
        "signature": function["type"]["qualType"],
    }


def parse_pop(function: AstNode) -> dict[str, Any]:
    body_children = expect_child_kinds(
        function_body(function),
        ("DeclStmt", "WhileStmt", "ReturnStmt"),
        "treiber_pop body",
    )
    _, observed_initializer = variable_declaration(
        body_children[0], "observed", "treiber_pop observed"
    )
    load = parse_atomic_load(
        observed_initializer,
        expected_order="acquire",
        result="observed",
        context="treiber_pop initial load",
    )

    loop = body_children[1]
    loop_children = expect_child_kinds(
        loop, ("BinaryOperator", "CompoundStmt"), "treiber_pop while"
    )
    condition = loop_children[0]
    require(
        condition.get("opcode") == "!=",
        "treiber_pop: expected observed != NULL loop condition",
    )
    condition_children = children(condition)
    require(len(condition_children) == 2, "treiber_pop: malformed loop condition")
    require(
        referenced_name(condition_children[0], "treiber_pop loop value")
        == "observed",
        "treiber_pop: loop must test observed",
    )
    expect_null_pointer(condition_children[1], "treiber_pop loop null")

    loop_body_children = expect_child_kinds(
        loop_children[1], ("DeclStmt", "IfStmt"), "treiber_pop loop body"
    )
    _, next_initializer = variable_declaration(
        loop_body_children[0], "next", "treiber_pop next"
    )
    next_expression = strip_expression(next_initializer)
    next_object = member_path(next_expression, "treiber_pop next read")
    require(
        next_object == "observed->next",
        "treiber_pop: expected observed->next read",
    )
    next_read = {
        "execution": "once_per_non_null_loop_attempt",
        "kind": "non_atomic_read",
        "object": next_object,
        "result": "next",
        "sequenced_before": "head_compare_exchange",
        "source": source_location(next_expression),
    }

    if_statement = loop_body_children[1]
    if_children = expect_child_kinds(
        if_statement, ("AtomicExpr", "CompoundStmt"), "treiber_pop CAS if"
    )
    compare_exchange = parse_weak_compare_exchange(
        if_children[0],
        expected_desired="next",
        expected_success_order="acquire",
        expected_failure_order="acquire",
        context="treiber_pop compare-exchange",
    )
    compare_exchange["loop_role"] = (
        "success_returns; failure_updates_observed_then_retests_loop"
    )

    success_body_children = expect_child_kinds(
        if_children[1], ("ReturnStmt",), "treiber_pop success body"
    )
    success_return = success_body_children[0]
    success_return_children = children(success_return)
    require(
        len(success_return_children) == 1,
        "treiber_pop: malformed success return",
    )
    require(
        referenced_name(success_return_children[0], "treiber_pop success return")
        == "observed",
        "treiber_pop: success must return observed",
    )

    empty_return = body_children[2]
    empty_return_children = children(empty_return)
    require(len(empty_return_children) == 1, "treiber_pop: malformed empty return")
    expect_null_pointer(empty_return_children[0], "treiber_pop empty return")

    return {
        "control_flow": {
            "loop": {
                "condition": "observed != null",
                "failure_path": (
                    "compare_exchange failure updates observed and reaches "
                    "the next loop test"
                ),
                "kind": "while",
                "retries_on": [
                    "weak_spurious_failure",
                    "head_value_mismatch",
                ],
            },
            "returns": [
                {
                    "condition": "head_compare_exchange_success",
                    "source": source_location(success_return),
                    "value": "observed",
                },
                {
                    "condition": "observed == null",
                    "source": source_location(empty_return),
                    "value": "null",
                },
            ],
        },
        "events": [
            {"id": "head_load", **load},
            {"id": "next_read", **next_read},
            {"id": "head_compare_exchange", **compare_exchange},
        ],
        "name": "treiber_pop",
        "parameters": function_parameters(function),
        "signature": function["type"]["qualType"],
    }


def parse_is_empty(function: AstNode) -> dict[str, Any]:
    body_children = expect_child_kinds(
        function_body(function), ("ReturnStmt",), "treiber_is_empty body"
    )
    return_statement = body_children[0]
    return_children = children(return_statement)
    require(len(return_children) == 1, "treiber_is_empty: malformed return")
    comparison = strip_expression(return_children[0])
    expect_kind(comparison, "BinaryOperator", "treiber_is_empty comparison")
    require(
        comparison.get("opcode") == "==",
        "treiber_is_empty: expected equality with null",
    )
    comparison_children = children(comparison)
    require(
        len(comparison_children) == 2,
        "treiber_is_empty: malformed equality",
    )
    load_node = comparison_children[0]
    expect_null_pointer(comparison_children[1], "treiber_is_empty null operand")
    load = parse_atomic_load(
        load_node,
        expected_order="acquire",
        result="head_snapshot",
        context="treiber_is_empty load",
    )
    return {
        "control_flow": {
            "return": {
                "expression": "head_snapshot == null",
                "source": source_location(return_statement),
            }
        },
        "events": [{"id": "head_load", **load}],
        "name": "treiber_is_empty",
        "parameters": function_parameters(function),
        "signature": function["type"]["qualType"],
    }


def clang_version(clang: Path) -> str:
    completed = subprocess.run(
        [str(clang), "--version"],
        check=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
    )
    match = re.search(r"\bclang version (\d+)\.(\d+)\.(\d+)", completed.stdout)
    require(match is not None, "could not parse Clang version")
    major = int(match.group(1))
    require(
        major == EXPECTED_CLANG_MAJOR,
        f"expected Clang {EXPECTED_CLANG_MAJOR}, found {match.group(0)}",
    )
    return ".".join(match.groups())


def load_ast(root: Path, clang: Path) -> AstNode:
    completed = subprocess.run(
        [str(clang), *AST_ARGS],
        cwd=root,
        check=False,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
    )
    require(
        completed.returncode == 0,
        "Clang AST extraction failed:\n" + completed.stderr.rstrip(),
    )
    try:
        return json.loads(completed.stdout)
    except json.JSONDecodeError as error:
        raise ExtractionError(f"Clang produced invalid AST JSON: {error}") from error


def defined_functions(ast: AstNode) -> dict[str, AstNode]:
    definitions: dict[str, AstNode] = {}
    for node in walk(ast):
        if kind(node) != "FunctionDecl":
            continue
        if not any(kind(child) == "CompoundStmt" for child in children(node)):
            continue
        name = node.get("name")
        if isinstance(name, str) and name.startswith("treiber_"):
            require(name not in definitions, f"duplicate definition of {name}")
            definitions[name] = node
    expected = {
        "treiber_init",
        "treiber_is_empty",
        "treiber_pop",
        "treiber_push",
    }
    require(
        set(definitions) == expected,
        f"expected definitions {sorted(expected)}, found {sorted(definitions)}",
    )
    return definitions


def validate_signatures(ast: AstNode) -> None:
    expected = {
        "treiber_init": "void (TreiberStack *)",
        "treiber_push": "void (TreiberStack *, TreiberNode *)",
        "treiber_pop": "TreiberNode *(TreiberStack *)",
        "treiber_is_empty": "_Bool (const TreiberStack *)",
    }
    for node in walk(ast):
        if kind(node) != "FunctionDecl" or node.get("name") not in expected:
            continue
        name = node["name"]
        actual = node.get("type", {}).get("qualType")
        require(
            actual == expected[name],
            f"{name}: expected signature {expected[name]!r}, found {actual!r}",
        )


def build_descriptor(root: Path, clang: Path) -> dict[str, Any]:
    source = root / "c/treiber.c"
    header = root / "c/treiber.h"
    require(source.is_file(), f"missing {source}")
    require(header.is_file(), f"missing {header}")
    header_text = header.read_text(encoding="utf-8")
    require(
        "never reclaimed or reused" in header_text,
        "treiber.h: missing the reclamation-free node-lifetime contract",
    )

    version = clang_version(clang)
    ast = load_ast(root, clang)
    validate_signatures(ast)
    functions = defined_functions(ast)

    descriptor = {
        "extractor": {
            "ast_arguments": list(AST_ARGS),
            "ast_format": "Clang JSON AST",
            "clang_required_major": EXPECTED_CLANG_MAJOR,
            "clang_version": version,
            "tool": "tools/extract_treiber_source_trust_boundary.py",
        },
        "initialization": parse_initialization(functions["treiber_init"]),
        "operations": [
            parse_push(functions["treiber_push"]),
            parse_pop(functions["treiber_pop"]),
            parse_is_empty(functions["treiber_is_empty"]),
        ],
        "schema": SCHEMA,
        "scope": {
            "atomic_object": "stack->head",
            "node_link": "TreiberNode.next",
            "node_lifetime_contract": "nodes are never reclaimed or reused",
            "public_operations": [
                "treiber_push",
                "treiber_pop",
                "treiber_is_empty",
            ],
        },
        "sources": [
            {
                "path": "c/treiber.c",
                "role": "implementation",
                "sha256": sha256(source),
            },
            {
                "path": "c/treiber.h",
                "role": "interface-and-lifetime-contract",
                "sha256": sha256(header),
            },
        ],
        "trust_boundary": {
            "classification": "explicitly-trusted-source-extraction",
            "claim": (
                "This descriptor is a deterministic check of a narrow "
                "Clang 18 AST shape; it is not a proved C semantics frontend."
            ),
            "consumer_obligation": (
                "Any formal source-to-model theorem must either trust this "
                "descriptor or independently validate its facts."
            ),
        },
    }
    return descriptor


def descriptor_bytes(descriptor: dict[str, Any]) -> bytes:
    return (
        json.dumps(
            descriptor,
            ensure_ascii=True,
            indent=2,
            sort_keys=True,
        )
        + "\n"
    ).encode("utf-8")


def lean_string(value: str) -> str:
    return json.dumps(value, ensure_ascii=True)


def lean_memory_order(value: str) -> str:
    orders = {
        "relaxed": ".relaxed",
        "acquire": ".acquire",
        "release": ".release",
        "acq_rel": ".acqRel",
        "seq_cst": ".seqCst",
    }
    require(value in orders, f"cannot render unknown memory order {value!r}")
    return orders[value]


def operation(descriptor: dict[str, Any], name: str) -> dict[str, Any]:
    matches = [
        entry for entry in descriptor["operations"] if entry["name"] == name
    ]
    require(len(matches) == 1, f"expected one descriptor operation {name}")
    return matches[0]


def event(operation_entry: dict[str, Any], event_id: str) -> dict[str, Any]:
    matches = [
        entry
        for entry in operation_entry["events"]
        if entry["id"] == event_id
    ]
    require(
        len(matches) == 1,
        f"{operation_entry['name']}: expected one event {event_id}",
    )
    return matches[0]


def lean_module_bytes(descriptor: dict[str, Any]) -> bytes:
    sources = {entry["path"]: entry for entry in descriptor["sources"]}
    require("c/treiber.c" in sources, "missing treiber.c source hash")
    require("c/treiber.h" in sources, "missing treiber.h source hash")

    push = operation(descriptor, "treiber_push")
    pop = operation(descriptor, "treiber_pop")
    is_empty = operation(descriptor, "treiber_is_empty")
    push_load = event(push, "head_load")
    pop_load = event(pop, "head_load")
    is_empty_load = event(is_empty, "head_load")
    push_cas = event(push, "head_compare_exchange")
    pop_cas = event(pop, "head_compare_exchange")
    push_next = event(push, "next_write")
    pop_next = event(pop, "next_read")

    require(
        descriptor["initialization"]["event"]["value"] == "null",
        "Lean descriptor requires null head initialization",
    )
    require(
        push_cas["strength"] == "weak" and pop_cas["strength"] == "weak",
        "Lean descriptor requires weak compare-exchanges",
    )
    require(
        push_cas["expected"]["failure_update"]["target"] == "observed"
        and pop_cas["expected"]["failure_update"]["target"] == "observed",
        "Lean descriptor requires expected-operand failure updates",
    )
    require(
        push_next["object"] == "node->next"
        and push_next["execution"] == "once_per_loop_attempt",
        "Lean descriptor requires the per-attempt push next write",
    )
    require(
        pop_next["object"] == "observed->next"
        and pop_next["execution"] == "once_per_non_null_loop_attempt",
        "Lean descriptor requires the per-attempt pop next read",
    )
    require(
        push["control_flow"]["loop"]["body_reexecuted_after_failure"] is True,
        "Lean descriptor requires push retry through the loop body",
    )
    require(
        "updates observed" in pop["control_flow"]["loop"]["failure_path"],
        "Lean descriptor requires pop expected update before retry",
    )
    require(
        push["control_flow"]["return"]["kind"] == "implicit_void",
        "Lean descriptor requires push void return",
    )
    require(
        [entry["value"] for entry in pop["control_flow"]["returns"]]
        == ["observed", "null"],
        "Lean descriptor requires pop success/null returns",
    )
    require(
        is_empty["control_flow"]["return"]["expression"]
        == "head_snapshot == null",
        "Lean descriptor requires the isEmpty null test",
    )

    rendered = f"""\
import WeakMemory.TreiberProgramDescriptor

/-!
This file is generated by
`tools/extract_treiber_source_trust_boundary.py`.

Do not edit it manually.  The value below crosses an explicitly trusted,
unproved Clang-AST extraction boundary; it is not evidence of a proved C
semantics frontend.
-/

namespace WeakMemory.TreiberProgramDescriptor.Extracted

/-- Hash-pinned facts extracted from the current reclamation-free C source. -/
def treiberProgram : PinnedExtraction where
  schema := {lean_string(descriptor["schema"])}
  clangVersion := {lean_string(descriptor["extractor"]["clang_version"])}
  cSourceSha256 := {lean_string(sources["c/treiber.c"]["sha256"])}
  cHeaderSha256 := {lean_string(sources["c/treiber.h"]["sha256"])}
  descriptor := {{
    initializesHeadToNull := true
    pushLoadOrder := {lean_memory_order(push_load["memory_order"])}
    popLoadOrder := {lean_memory_order(pop_load["memory_order"])}
    isEmptyLoadOrder := {lean_memory_order(is_empty_load["memory_order"])}
    pushCompareExchange := {{
      strength := .weak
      successOrder := {lean_memory_order(push_cas["success_memory_order"])}
      failureOrder := {lean_memory_order(push_cas["failure_memory_order"])}
      failureUpdatesExpected := true
    }}
    popCompareExchange := {{
      strength := .weak
      successOrder := {lean_memory_order(pop_cas["success_memory_order"])}
      failureOrder := {lean_memory_order(pop_cas["failure_memory_order"])}
      failureUpdatesExpected := true
    }}
    pushNextBehavior := .pushWritesObservedBeforeEveryAttempt
    popNextBehavior := .popReadsObservedNextBeforeEveryNonNullAttempt
    pushRetryBehavior := .pushUpdatesExpectedThenRewritesNext
    popRetryBehavior := .popUpdatesExpectedThenReadsNextOrReturnsNull
    pushReturnBehavior := .pushReturnsVoidAfterSuccess
    popReturnBehavior := .popReturnsObservedOnSuccessOrNullWhenEmpty
    isEmptyReturnBehavior := .isEmptyReturnsHeadNullTest
  }}

end WeakMemory.TreiberProgramDescriptor.Extracted
"""
    return rendered.encode("utf-8")


def check_output(
    output: Path, expected: bytes, description: str
) -> bool:
    if not output.is_file():
        print(f"ERROR: {description} is missing: {output}", file=sys.stderr)
        return False
    actual = output.read_bytes()
    if actual != expected:
        diff = difflib.unified_diff(
            actual.decode("utf-8", errors="replace").splitlines(),
            expected.decode("utf-8").splitlines(),
            fromfile=str(output),
            tofile="freshly extracted descriptor",
            lineterm="",
        )
        print(
            f"ERROR: {description} is stale or mismatched",
            file=sys.stderr,
        )
        print("\n".join(diff), file=sys.stderr)
        return False
    return True


def check_outputs(
    json_output: Path,
    expected_json: bytes,
    lean_output: Path,
    expected_lean: bytes,
) -> int:
    json_ok = check_output(
        json_output, expected_json, "trusted JSON source descriptor"
    )
    lean_ok = check_output(
        lean_output, expected_lean, "generated Lean source descriptor"
    )
    if not (json_ok and lean_ok):
        return 1
    decoded = json.loads(expected_json)
    hashes = {entry["path"]: entry["sha256"] for entry in decoded["sources"]}
    print(
        "OK: JSON and Lean descriptors match "
        f"Clang {decoded['extractor']['clang_version']} AST"
    )
    print(f"JSON: {json_output}")
    print(f"Lean: {lean_output}")
    print(f"c/treiber.c sha256 {hashes['c/treiber.c']}")
    print(f"c/treiber.h sha256 {hashes['c/treiber.h']}")
    return 0


def parse_args() -> argparse.Namespace:
    script = Path(__file__).resolve()
    root = script.parents[1]
    default_clang = (
        root.parent / ".tools/llvm18-root/usr/lib/llvm-18/bin/clang"
    )
    parser = argparse.ArgumentParser(
        description=(
            "Extract or check the explicitly trusted Treiber source "
            "descriptor from Clang 18 AST JSON."
        )
    )
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument(
        "--check",
        action="store_true",
        help="fail unless the checked-in descriptor exactly matches extraction",
    )
    mode.add_argument(
        "--stdout",
        action="store_true",
        help="write the normalized descriptor to stdout",
    )
    parser.add_argument(
        "--clang",
        type=Path,
        default=default_clang,
        help=f"Clang 18 executable (default: {default_clang})",
    )
    parser.add_argument(
        "--output",
        type=Path,
        default=root / DEFAULT_DESCRIPTOR,
        help=f"JSON descriptor path (default: {root / DEFAULT_DESCRIPTOR})",
    )
    parser.add_argument(
        "--lean-output",
        type=Path,
        default=root / DEFAULT_LEAN_OUTPUT,
        help=(
            "generated Lean descriptor path "
            f"(default: {root / DEFAULT_LEAN_OUTPUT})"
        ),
    )
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    script = Path(__file__).resolve()
    root = script.parents[1]
    clang = args.clang.resolve()
    require(clang.is_file(), f"missing Clang executable: {clang}")
    descriptor = build_descriptor(root, clang)
    expected_json = descriptor_bytes(descriptor)
    expected_lean = lean_module_bytes(descriptor)

    if args.stdout:
        sys.stdout.buffer.write(expected_json)
        return 0
    json_output = args.output.resolve()
    lean_output = args.lean_output.resolve()
    if args.check:
        return check_outputs(
            json_output,
            expected_json,
            lean_output,
            expected_lean,
        )

    for output, expected in (
        (json_output, expected_json),
        (lean_output, expected_lean),
    ):
        output.parent.mkdir(parents=True, exist_ok=True)
        temporary = output.with_name(output.name + ".tmp")
        temporary.write_bytes(expected)
        temporary.replace(output)
        print(f"wrote {output}")
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (ExtractionError, OSError, subprocess.SubprocessError) as error:
        print(f"ERROR: {error}", file=sys.stderr)
        raise SystemExit(2) from error
