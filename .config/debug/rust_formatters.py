"""Rust formatters for lldb on this checkout (#3760).

`.config/debug/lldbinit` imports this module. It loads rustc's own formatters
from the pinned toolchain's `lib/rustlib/etc`, then corrects two defects that
make a sum-type enum print the wrong variant:

- lldb places an enum's `$discr$` member at offset 0, its byte offset kept as a
  bit-field width. Where the tag sits past offset 0, the formatters read the
  wrong bytes and fall back to the dataful variant. The correction reads the
  tag at its true offset.
- rustc's formatters register an enum's summary the first time they meet the
  enum by value. A reference or a box met first prints every variant raw, the
  dataful one first. The correction registers the summary and the children of
  every sum-type enum, by a type recognizer, when the module loads.
"""

import os
import shlex
import sys
from typing import Optional

import lldb

VARIANTS = "$variants$"
DISCRIMINANT = "$discr$"


def _rustlib_etc(debugger: lldb.SBDebugger) -> str:
    """The pinned toolchain's formatter directory, read from this checkout.

    lldb's platform shell runs `rustc`, never Python's `subprocess`: lldb's
    embedded Python may meet a standard library built for another
    interpreter, whose `_posixsubprocess` does not load.
    """
    checkout = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
    result = lldb.SBCommandReturnObject()
    debugger.GetCommandInterpreter().HandleCommand(
        f"platform shell -h -s /bin/sh -- env -C {shlex.quote(checkout)} rustc --print sysroot", result
    )
    etc = os.path.join(result.GetOutput().strip(), "lib", "rustlib", "etc")
    if not result.Succeeded() or not os.path.isfile(os.path.join(etc, "lldb_lookup.py")):
        raise RuntimeError(f"`rustc --print sysroot` in {checkout} names no formatters: {result.GetOutput()}{result.GetError()}")
    return etc


def discriminant(variant: lldb.SBValue) -> Optional[int]:
    """The tag a `$variant$` member reads, or None for the dataful variant.

    lldb keeps the tag's byte offset as the member's bit-field width and lays
    the member at offset 0. A member that is no bit-field sits where lldb
    says, at offset 0 or at an offset a corrected lldb reports.
    """
    variant_type = variant.GetType()
    for index in range(variant_type.GetNumberOfFields()):
        field = variant_type.GetFieldAtIndex(index)
        if field.GetName() == DISCRIMINANT:
            offset = field.GetBitfieldSizeInBits() if field.IsBitfield() else field.GetOffsetInBytes()
            return variant.CreateChildAtOffset(DISCRIMINANT, offset, field.GetType()).GetValueAsUnsigned()
    return None


def current_variant_index(_provider, all_variants: lldb.SBValue) -> int:
    """The index of the variant whose tag the value holds, else the dataful one."""
    dataful = 0
    for index in range(all_variants.GetNumChildren()):
        variant = all_variants.GetChildAtIndex(index)
        tag = discriminant(variant)
        if tag is None:
            dataful = index
        elif variant.GetName() == f"$variant${tag}":
            return index
    return dataful


def is_sum_enum(sbtype: lldb.SBType, _dict) -> bool:
    """A sum-type enum as lldb lays it out: one `$variants$` member."""
    return sbtype.GetNumberOfFields() == 1 and sbtype.GetFieldAtIndex(0).GetName() == VARIANTS


def __lldb_init_module(debugger: lldb.SBDebugger, _dict) -> None:
    etc = _rustlib_etc(debugger)
    debugger.HandleCommand(f'command script import "{os.path.join(etc, "lldb_lookup.py")}"')
    providers = sys.modules["lldb_providers"]
    lookup = sys.modules["lldb_lookup"]
    if not hasattr(providers.ClangEncodedEnumProvider, "_getCurrentVariantIndex"):
        raise RuntimeError(
            f"{etc}/lldb_providers.py no longer picks an enum's variant in "
            "`ClangEncodedEnumProvider._getCurrentVariantIndex`; port `current_variant_index` to it"
        )
    providers.ClangEncodedEnumProvider._getCurrentVariantIndex = current_variant_index

    category = debugger.GetCategory("Rust")
    recognizer = lldb.SBTypeNameSpecifier(f"{__name__}.{is_sum_enum.__name__}", lldb.eFormatterMatchCallback)
    summary = lldb.SBTypeSummary.CreateWithFunctionName("lldb_lookup.ClangEncodedEnumSummaryProvider")
    summary.SetOptions(lookup.DEFAULT_TYPE_OPTIONS)
    category.AddTypeSummary(recognizer, summary)
    synthetic = lldb.SBTypeSynthetic.CreateWithClassName("lldb_lookup.ClangEncodedEnumProvider")
    synthetic.SetOptions(lookup.DEFAULT_TYPE_OPTIONS)
    category.AddTypeSynthetic(recognizer, synthetic)
