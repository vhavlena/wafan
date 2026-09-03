"""Where a target spec reads from, and how it filters.

Several specs read the same members: ``ARGS``, ``ARGS:id``, ``ARGS:/re/`` and
``ARGS_NAMES`` all resolve to members of ``ARGS``, differing only in which
field the operator sees and which members are admitted. Resolving them onto a
common *family* here, rather than folding the selector into the SMT symbol, is
what lets both encoders express the relations between them by construction:
``ARGS:id`` is a subset of ``ARGS`` because it is literally the same members,
filtered, and two rules reading them can be asked whether they match one
*common* member rather than merely coexisting in one request.

This module is deliberately dependency-free (beyond the parser) so that both
the stateless encoder (``wafan.smt``) and the stateful one (``wafan.state``)
can share it.
"""

from __future__ import annotations

import re
from dataclasses import dataclass

from .parser import SecRuleVariable


# Collections that can hold more than one member in a single transaction, and
# so are modelled as a bounded array by the stateful encoder. Everything not
# listed here --- REQUEST_METHOD, REQUEST_URI, REQUEST_FILENAME, RESPONSE_BODY,
# … --- holds exactly one value and stays a single constant.
#
# The default matters: unrolling a genuine scalar would let two conditions in
# one chain be satisfied by two different "members" of something that has only
# one, inventing requests that cannot exist (a chain requiring
# REQUEST_METHOD to be both GET and POST would come out satisfiable). Treating
# an unlisted collection as scalar instead merely reproduces the older,
# single-representative behaviour, so an omission from this list costs
# precision rather than soundness.
MULTI_VALUED_COLLECTIONS = frozenset({
    "ARGS", "ARGS_NAMES", "ARGS_GET", "ARGS_GET_NAMES", "ARGS_POST",
    "ARGS_POST_NAMES", "REQUEST_HEADERS", "REQUEST_HEADERS_NAMES",
    "REQUEST_COOKIES", "REQUEST_COOKIES_NAMES", "RESPONSE_HEADERS",
    "RESPONSE_HEADERS_NAMES", "FILES", "FILES_NAMES", "FILES_SIZES",
    "FILES_TMPNAMES", "FILES_TMP_CONTENT", "MULTIPART_FILENAME",
    "MULTIPART_NAME", "MATCHED_VARS", "MATCHED_VARS_NAMES", "XML", "ENV",
})


# A "_NAMES" collection is not a collection of its own: it is a view over the
# member *names* of its base. Mapping it onto the same family is what makes
# `&ARGS` and `&ARGS_NAMES` agree, and lets one chain link match a parameter's
# name while another matches its value.
NAMES_VIEW_OF = {
    "ARGS_NAMES": "ARGS",
    "ARGS_GET_NAMES": "ARGS_GET",
    "ARGS_POST_NAMES": "ARGS_POST",
    "REQUEST_HEADERS_NAMES": "REQUEST_HEADERS",
    "REQUEST_COOKIES_NAMES": "REQUEST_COOKIES",
    "RESPONSE_HEADERS_NAMES": "RESPONSE_HEADERS",
    "FILES_NAMES": "FILES",
    "MATCHED_VARS_NAMES": "MATCHED_VARS",
}

# Collections whose selector is a member *name*, so that `COLL:sel` can be
# encoded as a filter over the shared family. XML is excluded: its selector is
# an XPath expression (`XML:/*`), not a name, so each XML target keeps a
# family of its own.
_NOT_NAME_KEYED = frozenset({"XML"})

# Collections whose member names are compared case-insensitively. HTTP header
# names are, per RFC 7230; query-parameter names are not.
CASE_INSENSITIVE_NAMES = frozenset({"REQUEST_HEADERS", "RESPONSE_HEADERS"})


def is_multi_valued(variable: SecRuleVariable) -> bool:
    """True if *variable*'s collection can hold several members at once."""
    return variable.name.upper() in MULTI_VALUED_COLLECTIONS


def is_name_keyed(variable: SecRuleVariable) -> bool:
    """True if *variable*'s selector filters member names of a shared family.

    False for a scalar (nothing to filter) and for ``XML`` (whose selector is
    an XPath expression), both of which keep the selector folded into their
    symbol instead.
    """
    return is_multi_valued(variable) and variable.name.upper() not in _NOT_NAME_KEYED


@dataclass(frozen=True)
class TargetRef:
    """A target spec resolved onto its backing family and filter."""

    family: str        # SMT-safe name of the backing collection
    multi: bool        # several members, or a lone value
    reads_names: bool  # the operator sees the member name, not its value
    selector: str      # "" for the whole collection
    selector_is_regex: bool
    fold_case: bool    # compare names case-insensitively


def sanitise_symbol(text: str) -> str:
    """Replace anything outside ``[A-Za-z0-9_]`` with its hex codepoint."""
    return re.sub(r"[^A-Za-z0-9_]", lambda m: f"_x{ord(m.group()):02x}_", text)


def resolve_target(variable: SecRuleVariable) -> TargetRef:
    """Map a target spec onto its backing family and filter."""
    name = variable.name.upper()
    part = variable.part

    if not is_multi_valued(variable) or name in _NOT_NAME_KEYED:
        # Scalars, and collections whose selector is not a member name, keep
        # the selector folded into the symbol: there is nothing to filter.
        return TargetRef(
            family=smt_var_name(variable),
            multi=is_multi_valued(variable),
            reads_names=False,
            selector="",
            selector_is_regex=False,
            fold_case=False,
        )

    base = NAMES_VIEW_OF.get(name, name)
    is_regex = part.startswith("/") and part.endswith("/") and len(part) > 1
    return TargetRef(
        family=sanitise_symbol(base),
        multi=True,
        reads_names=name in NAMES_VIEW_OF,
        selector=part[1:-1] if is_regex else part,
        selector_is_regex=is_regex,
        fold_case=base in CASE_INSENSITIVE_NAMES,
    )


def smt_var_name(variable: SecRuleVariable) -> str:
    """Produce a sanitised SMT identifier for a whole ModSecurity variable spec.

    ``variable.part`` may itself be a regex (e.g. ``ARGS:/jform\\[pass\\]/``),
    which can contain characters like ``/[]\\`` that are not valid in an
    unquoted SMT-LIB2 simple symbol. Anything outside ``[A-Za-z0-9_]`` is
    replaced with its hex codepoint (e.g. ``[`` -> ``_x5b_``) rather than a
    single ``_``, so two different variable specs that merely differ in
    which non-alnum characters they contain (e.g. ``ARGS:a.b`` vs
    ``ARGS:a_b``) can't collide onto the same SMT identifier.

    This folds the selector into the symbol, and so is only right for specs
    that :func:`resolve_target` cannot key by name (scalars, ``XML``); for
    everything else the selector is a filter over a shared family, and
    encoders should go through :func:`resolve_target`.
    """
    name = variable.name
    if variable.part:
        name = f"{name}__{variable.part}"
    return sanitise_symbol(name)
